module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.GenWide
public import VerifiedGarbage.Impl.X448.RISCV64.R64
public import VerifiedGarbage.Impl.Words.RISCV64.Wide

/-!
# Montgomery's multiplication modulo P-521's prime by its Mersenne form, on RISC-V

`vg_p521_mul_mod_p(ws, o, a, b)` meets the same contract as GenWide's
(`Proof/Weierstrass/MontContract.lean`: `[o] R ≡ [a] [b]` modulo
`p = 2⁵²¹ - 1`, `R = 2⁵⁷⁶`, `[o] < p`, for `[b] < p` and any nine words
`[a]`), with GenWide's entry and copies (`GenWide.fn`), but no reduction by
`p`'s words: as `2⁵²¹ ≡ 1`, `R⁻¹ ≡ 2⁴⁶⁶`, and

1. `T = [a] [b]`, eighteen words at `T`, by columns (`productC`): column
   `k`'s terms `a_i b_j` (`i + j = k`) added to a three-word accumulator in
   registers (rotating through `a4`–`a6`, as X448's `rr`), then its low word
   stored as `T[k]`; each term's product is computed, and the next one's
   operands loaded, a term ahead of its sums, so that an in-order processor
   does not wait for them;
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
open VG.Impl.Weierstrass.RISCV64.GenWide (T adcCore fn fnA)
open VG.Impl.X448.RISCV64.R64 (rr)

/-- The base of the eighteen words of the product, from `a3`. -/
abbrev P : Nat := T 9

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

/-! ## The product by columns, software-pipelined -/

/-- The terms `(i, j)` of column `k` of a product of nine words, `i` descending. -/
def colPairs (k : Nat) : List (Nat × Nat) :=
  ((List.range 9).reverse.filter fun i => i ≤ k ∧ k - i < 9).map fun i => (i, k - i)

/-- The product's 81 terms `(k, i, j)`, column by column. -/
def terms : List (Nat × Nat × Nat) :=
  (List.range 18).flatMap fun k => (colPairs k).map fun p => (k, p.1, p.2)

/-- Term `n`. -/
def term (n : Nat) : Nat × Nat × Nat := terms.getD n (0, 0, 0)

/-- The index of column `k`'s first term. -/
def start (k : Nat) : Nat := ((List.range k).map fun c => (colPairs c).length).sum

/-- The registers of term `n`'s product, low and high: `a7`, `t0` and `t3`,
`t6` in turn. -/
def PR (n : Nat) : Reg × Reg := if n % 2 = 0 then (.a7, .t0) else (.t3, .t6)

/-- Term `n`'s operands, `a_i` into `a1` and `b_j` into `a2`, if it is one. -/
def ldNext (n : Nat) : List Instr :=
  if n < 81 then [.load .d .a1 .t4 (8 * (term n).2.1), .load .d .a2 .t5 (8 * (term n).2.2)] else []

/-- Term `n`'s product, from `a1` and `a2`, if it is one. -/
def mulNext (n : Nat) : List Instr :=
  if n < 81 then VG.Impl.Words.RISCV64.mulWide (PR n).1 (PR n).2 .a1 .a2 else []

/-- Term `n`'s product added to column `k`'s three-word accumulator. -/
def accum (k n : Nat) : List Instr :=
  [.add (rr k) (rr k) (PR n).1, .sltu (PR n).1 (rr k) (PR n).1, .add (PR n).2 (PR n).2 (PR n).1,
    .add (rr (k + 1)) (rr (k + 1)) (PR n).2, .sltu (PR n).2 (rr (k + 1)) (PR n).2,
    .add (rr (k + 2)) (rr (k + 2)) (PR n).2]

/-- Term `n`, of column `k`: the next term's product and the operands of the
one after it, issued before this one's sums, which they do not depend on. -/
def step (k n : Nat) : List Instr := mulNext (n + 1) ++ ldNext (n + 2) ++ accum k n

/-- Column `k`: its terms, its low word stored as `T[k]`, and the register zeroed. -/
def mulCol (k : Nat) : List Instr :=
  (List.range' (start k) (colPairs k).length).flatMap (step k) ++ [.store .d (rr k) .a3 (P + 8 * k), .li (rr k) 0]

/-- `T = [t4] [t5]`, eighteen words, by columns, the first term's product and
the second's operands ahead. -/
def productC : List Instr :=
  [.li .a4 0, .li .a5 0, .li .a6 0] ++ ldNext 0 ++ mulNext 0 ++ ldNext 1 ++ (List.range 18).flatMap mulCol

/-- `[t2] = [t4] [t5] R⁻¹ mod p`. -/
def mulCore : List Instr := productC ++ fold ++ fold2 ++ canon ++ rot

/-- The function multiplying modulo `p`. -/
def mulFn : Prog isa := fn 9 mulCore

/-- `vg_p521_mul_mod_p`, for aligned offsets. -/
def mulFnA : Prog isa := fnA (.block mulCore)

end VG.Impl.Weierstrass.RISCV64.P521Mersenne
