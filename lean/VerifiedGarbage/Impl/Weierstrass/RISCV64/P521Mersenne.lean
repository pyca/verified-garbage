module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.GenWide

/-!
# Montgomery's multiplication modulo P-521's prime by its Mersenne form, on RISC-V

`vg_p521_mul_mod_p(ws, o, a, b)` meets the same contract as GenWide's
(`Proof/Weierstrass/MontContract.lean`: `[o] R ≡ [a] [b]` modulo
`p = 2⁵²¹ - 1`, `R = 2⁵⁷⁶`, `[o] < p`, for `[b] < p` and any nine words
`[a]`), with GenWide's entry and copies (`GenWide.fn`), but no reduction by
`p`'s words: as `2⁵²¹ ≡ 1`, `R⁻¹ ≡ 2⁴⁶⁶`, and

1. `T = [a] [b]`, eighteen words at `T` (`prodRow`: for each word `bᵢ`,
   `T[i…i+8] += a bᵢ` by GenWide's `macStep`, its carry stored as `T[i+9]`);
2. `s = (T mod 2⁵²¹) + (T >> 521)`, nine words and the carry `c` (`fold`),
   in place;
3. `s₂ = (s mod 2⁵²¹) + (s >> 521)` (`fold2`), below `2⁵²¹ + 2⁵⁶`;
4. `r = (s₂ + q) mod 2⁵²¹`, with `q` the bit 521 of `s₂ + 1` (`canon`): the
   residue of `[a] [b]` below `p`;
5. `[o] = r 2⁴⁶⁶ mod p`, the rotation of `r`'s 521 bits right by 55
   (`rot`).

Every multiplication is `mul` or `mulhu`, and there is no branch but
GenWide's on the pointers.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64.P521Mersenne

open VG.RISCV64
open VG.Impl.Weierstrass.RISCV64.GenWide (T macStep adcCore fn fnA)

/-- The base of the eighteen words of the product, from `a3`. -/
abbrev P : Nat := T 9

/-- `T[0…8] = 0`, through `a7`. -/
def zeroT : List Instr :=
  .li .a7 0 :: (List.range 9).map fun j => .store .d .a7 .a3 (P + 8 * j)

/-- `T[i…i+8] += a bᵢ`, the carry stored as `T[i+9]`. -/
def prodRow (i : Nat) : List Instr :=
  [.load .d .a4 .t5 (8 * i), .li .a5 0] ++
    (List.range 9).flatMap (fun j => macStep .t4 (8 * j) (P + 8 * i + 8 * j) (P + 8 * i + 8 * j)) ++
    [.store .d .a5 .a3 (P + 8 * i + 8 * 9)]

/-- Word `j` of `T >> 521` into `a7`: `(T[8+j] >> 9) | (T[9+j] << 55)`, through `t0`. -/
def hiWord (j : Nat) : List Instr :=
  [.load .d .a7 .a3 (P + 8 * (8 + j)), .load .d .t0 .a3 (P + 8 * (9 + j)), .shift .srl .d .a7 .a7 9,
    .shift .sll .d .t0 .t0 55, .logic .or .a7 .a7 .t0]

/-- Word `j < 8` of `s = (T mod 2⁵²¹) + (T >> 521)` into `T[j]`, the carry in `a5`. -/
def foldStep (j : Nat) : List Instr :=
  hiWord j ++ [.load .d .a6 .a3 (P + 8 * j)] ++ adcCore ++ [.store .d .t0 .a3 (P + 8 * j)]

/-- Word 8 of `s`, from the nine low bits of `T[8]`. -/
def foldTop : List Instr :=
  hiWord 8 ++ [.load .d .a6 .a3 (P + 64), .logicImm .and .a6 .a6 0x1ff] ++ adcCore ++ [.store .d .t0 .a3 (P + 64)]

/-- `s`, nine words in `T[0…8]`, and its carry `c` in `a5`. -/
def fold : List Instr := .li .a5 0 :: (List.range 8).flatMap foldStep ++ foldTop

/-- `[a3 + P + 8 j] += a5`, the carry out in `a5`, through `t0` and `t3`. -/
def carryStep (j : Nat) : List Instr :=
  [.load .d .t0 .a3 (P + 8 * j), .add .t0 .t0 .a5, .sltu .a5 .t0 .a5, .store .d .t0 .a3 (P + 8 * j)]

/-- `s₂ = (s mod 2⁵²¹) + (s >> 521)`: `(s₈ >> 9) | (c << 55)` into `a5`,
`s₈` cut to its nine bits, then the carries through the nine words. -/
def fold2 : List Instr :=
  [.load .d .t0 .a3 (P + 64), .shift .srl .d .a6 .t0 9, .shift .sll .d .a5 .a5 55, .logic .or .a5 .a5 .a6,
    .logicImm .and .t0 .t0 0x1ff, .store .d .t0 .a3 (P + 64)] ++ (List.range 9).flatMap carryStep

/-- The carry of `[a3 + P + 8 j] + a5` into `a5`, through `t0`. -/
def probeStep (j : Nat) : List Instr :=
  [.load .d .t0 .a3 (P + 8 * j), .add .t0 .t0 .a5, .sltu .a5 .t0 .a5]

/-- `r = (s₂ + q) mod 2⁵²¹`, `q` the bit 521 of `s₂ + 1`: the carry of `+1`
through words 0…7, added to word 8, whose bit 9 is `q`, into `a5`; then `q`
added, and word 8 cut to nine bits. -/
def canon : List Instr :=
  [.li .a5 1] ++ (List.range 8).flatMap probeStep ++
    [.load .d .t0 .a3 (P + 64), .add .t0 .t0 .a5, .shift .srl .d .a5 .t0 9] ++
    (List.range 9).flatMap carryStep ++
    [.load .d .t0 .a3 (P + 64), .logicImm .and .t0 .t0 0x1ff, .store .d .t0 .a3 (P + 64)]

/-- `(r_j >> 55) | (r_{j+1} << 9)` into `t0`, through `a6`. -/
def rotWord (j : Nat) : List Instr :=
  [.load .d .t0 .a3 (P + 8 * j), .load .d .a6 .a3 (P + 8 * (j + 1)), .shift .srl .d .t0 .t0 55,
    .shift .sll .d .a6 .a6 9, .logic .or .t0 .t0 .a6]

/-- Word `j < 7` of `[o]`, `r` rotated right by 55 of its 521 bits. -/
def rotStep (j : Nat) : List Instr := rotWord j ++ [.store .d .t0 .t2 (8 * j)]

/-- Words 7 and 8 of `[o]`: `(r₇ >> 55) | (r₈ << 9) | (r₀ << 18)`, and bits
46…54 of `r₀`. -/
def rotTop : List Instr :=
  rotWord 7 ++ [.load .d .a6 .a3 P, .shift .sll .d .a6 .a6 18, .logic .or .t0 .t0 .a6, .store .d .t0 .t2 56,
    .load .d .t0 .a3 P, .shift .srl .d .t0 .t0 46, .logicImm .and .t0 .t0 0x1ff, .store .d .t0 .t2 64]

/-- `[o] = r 2⁴⁶⁶ mod p`. -/
def rot : List Instr := (List.range 7).flatMap rotStep ++ rotTop

/-- `[t2] = [t4] [t5] R⁻¹ mod p`. -/
def mulCore : List Instr :=
  zeroT ++ (List.range 9).flatMap prodRow ++ fold ++ fold2 ++ canon ++ rot

/-- The function multiplying modulo `p`. -/
def mulFn : Prog isa := fn 9 mulCore

/-- `vg_p521_mul_mod_p`, for aligned offsets. -/
def mulFnA : Prog isa := fnA (.block mulCore)

end VG.Impl.Weierstrass.RISCV64.P521Mersenne
