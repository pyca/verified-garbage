module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P256Field
public import VerifiedGarbage.Impl.Words.RISCV64.Word64

/-!
# Arithmetic modulo any odd modulus of seven words or more, as functions, on RISC-V

`vg_<name>_{mul,add,sub}_mod_<m>(ws, o, a, b)` (`Proof/Weierstrass/MontContract.lean`;
`ws` in `a0`, the offsets in the low words of `a1`–`a3`) for numbers of `k`
64-bit words, `k ≥ 7`, and an odd modulus `m < 2^(64 k)` known when the code
is generated. Their own working space is the top `64 k` bytes of `ws`
(`Proof/Weierstrass/RISCV64/FieldRV.lean`'s `rvOwn`), which `a3 = ws + 6144`
reaches with short offsets (`T`, `N`, `SA`, `SB`, `SO`).

Too few registers hold `k` words, so the running value lives in memory, at
`T` (`k + 2` words), and every operation streams its operands from memory:

1. the offsets are zero-extended, and `t2`, `t4` and `t5` point to `[o]`,
   `[a]` and `[b]` (P-256's `zext` and pointers, `ptrs`), `a3` to
   `ws + 6144`; as P-256's and P-384's, the operands are copied a byte at a
   time into the own working space when a pointer is not a multiple of 8
   (`fn`), the result copied back to `[o]`, whose pointer the copies keep in
   `t1`;
2. `m`'s words are stored at `N` (`fillN`, each built by `li64`);
3. the operation:
   * `mulCore`: Montgomery's multiplication by operand scanning (CIOS): for
     each word `bᵢ`, `T += a bᵢ` (`macStep` with `a`'s words), then the
     quotient word `q = T₀ m' mod 2⁶⁴` (`m' = -m⁻¹ mod 2⁶⁴`, in `t6`) and
     `T = (T + q m) / 2⁶⁴` (`macStep` with `m`'s words, each word stored one
     word down); after `k` rounds `T`, below `2 m`, is reduced by `csub`;
   * `addCore`: the sum with carries into `T`, then `csub`;
   * `subCore`: the difference with borrows into `T`, and `m` added back
     under the mask of the borrow, into `[o]`.
   `csub`: `T - m` with borrows over `N`, whose words are no longer needed,
   and, word by word, that difference or `T` by the mask `T_k - borrow`
   (all ones exactly when `T < m`), into `[o]`.

Every multiplication is `mul` or `mulhu`, every selection a mask, and the
only branch is on the pointers, which are public, as every address is a
pointer plus a constant. The functions use only caller-saved registers and
no stack, and write only `[o]` and their own working space.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64.GenWide

open VG.RISCV64
open VG.Impl.Words.RISCV64 (li64)

/-- Word `j` of `x`. -/
def wordOf (x j : Nat) : BitVec 64 := BitVec.ofNat 64 (x >>> (64 * j))

/-- `-x⁻¹ mod 2⁶⁴` for an odd `x`, by Newton's iteration from `x` (correct
to three bits), each step doubling the correct bits. -/
def negInv (x : Nat) : Nat :=
  let step := fun (y : Nat) => y * (2 + 2 ^ 64 - x * y % 2 ^ 64) % 2 ^ 64
  (2 ^ 64 - step (step (step (step (step x % 2 ^ 64))))) % 2 ^ 64

variable (k m : Nat)

/-! ## Layout, from `a3 = ws + 6144` -/

/-- The running value, `k + 2` words, at the start of the own working space. -/
def T : Nat := 2048 - 64 * k

/-- The modulus's words, and in `csub` the difference. -/
def N : Nat := T k + 8 * (k + 2)

/-- The byte-wise copies of the operands and the result, for offsets that
are not multiples of 8. -/
def SA : Nat := N k + 8 * k
def SB : Nat := SA k + 8 * k
def SO : Nat := SB k + 8 * k

/-! ## Entry -/

/-- `t2 = ws + o`, `t4 = ws + a`, `t5 = ws + b`, `a3 = ws + 6144`, and in `t0`
the low three bits of the pointers or'ed. -/
def ptrs : List Instr :=
  [.add .t2 .a0 .a1, .add .t4 .a0 .a2, .add .t5 .a0 .a3, .addi .a3 .a0 2047, .addi .a3 .a3 2047,
    .addi .a3 .a3 2047, .addi .a3 .a3 3, .logic .or .t0 .t2 .t4, .logic .or .t0 .t0 .t5,
    .logicImm .and .t0 .t0 7]

/-- `m`'s words at `N`, through `a6` and `a7`. -/
def fillN : List Instr :=
  (List.range k).flatMap fun j => li64 .a6 .a7 (wordOf m j) ++ [.store .d .a6 .a3 (N k + 8 * j)]

/-! ## Montgomery's multiplication -/

/-- `t0 + 2⁶⁴ a5 := x · a4 + [a3 + ti] + a5`, the word `x` at `xb + xo` in
`a6`, `[a3 + ti]` in `a7`, the low word stored at `a3 + to`, through `a1`
and `t3`. -/
def macStep (xb : Reg) (xo ti to : Nat) : List Instr :=
  [.load .d .a6 xb xo, .load .d .a7 .a3 ti, .mul .t0 .a6 .a4, .mulhu .a1 .a6 .a4,
    .add .t0 .t0 .a7, .sltu .t3 .t0 .a7, .add .a1 .a1 .t3,
    .add .t0 .t0 .a5, .sltu .t3 .t0 .a5, .add .a5 .a1 .t3, .store .d .t0 .a3 to]

/-- `T += a bᵢ`: `bᵢ` into `a4`, the carry `a5` zero, the steps over `a`'s
words, then the carry into `T_k` and its carry stored as `T_{k+1}`. -/
def mulRound (i : Nat) : List Instr :=
  [.load .d .a4 .t5 (8 * i), .li .a5 0] ++
    (List.range k).flatMap (fun j => macStep .t4 (8 * j) (T k + 8 * j) (T k + 8 * j)) ++
    [.load .d .a7 .a3 (T k + 8 * k), .add .t0 .a7 .a5, .sltu .t3 .t0 .a5, .store .d .t0 .a3 (T k + 8 * k),
      .store .d .t3 .a3 (T k + 8 * (k + 1))]

/-- `T = (T + q m) / 2⁶⁴` for `q = T₀ m'` (into `a4`): the high word of `q m₀`
plus the carry of `T₀ + (q m₀ mod 2⁶⁴)`, which is `T₀ ≠ 0`, into `a5`, then
the steps over `m`'s words `1 … k - 1`, each stored one word down, and the
carries into `T_{k-1}` and `T_k`. -/
def redRound : List Instr :=
  [.load .d .a7 .a3 (T k), .mul .a4 .a7 .t6, .load .d .a6 .a3 (N k), .mulhu .a5 .a4 .a6, .li .t3 0,
    .sltu .t3 .t3 .a7, .add .a5 .a5 .t3] ++
    (List.range (k - 1)).flatMap (fun j => macStep .a3 (N k + 8 * (j + 1)) (T k + 8 * (j + 1)) (T k + 8 * j)) ++
    [.load .d .a7 .a3 (T k + 8 * k), .add .t0 .a7 .a5, .sltu .t3 .t0 .a5, .store .d .t0 .a3 (T k + 8 * (k - 1)),
      .load .d .a7 .a3 (T k + 8 * (k + 1)), .add .a7 .a7 .t3, .store .d .a7 .a3 (T k + 8 * k)]

/-- `T` zero (words `0 … k`), and `m'` into `t6`, through `a7`. -/
def mulInit : List Instr :=
  .li .a7 0 :: (List.range (k + 1)).map (fun j => .store .d .a7 .a3 (T k + 8 * j)) ++
    li64 .t6 .a7 (BitVec.ofNat 64 (negInv m))

/-! ## The final subtraction -/

/-- `[a3 + d] := [a3 + x] - [a3 + y] - a5`, the borrow in and out in `a5`, through
`a6`, `a7`, `t0`, `t3` and `a1`. -/
def sbbStep (xb : Reg) (xo : Nat) (yb : Reg) (yo : Nat) (db : Reg) (d : Nat) : List Instr :=
  [.load .d .a7 xb xo, .load .d .a6 yb yo, .sub .t0 .a7 .a6, .sltu .t3 .a7 .a6, .sltu .a1 .t0 .a5,
    .sub .t0 .t0 .a5, .logic .or .a5 .t3 .a1, .store .d .t0 db d]

/-- Word `j` of `[o]`: `N`'s (the difference) if the mask `a7` is zero, `T`'s if
it is all ones, through `t0` and `a6`. -/
def selStep (j : Nat) : List Instr :=
  [.load .d .t0 .a3 (N k + 8 * j), .load .d .a6 .a3 (T k + 8 * j), .logic .xor .a6 .a6 .t0,
    .logic .and .a6 .a6 .a7, .logic .xor .t0 .t0 .a6, .store .d .t0 .t2 (8 * j)]

/-- `[o] = T mod m`, for `T < 2 m`: `T - m` over `N`, the mask `T_k - borrow`
into `a7`, and the selection. -/
def csub : List Instr :=
  [.li .a5 0] ++ (List.range k).flatMap (fun j => sbbStep .a3 (T k + 8 * j) .a3 (N k + 8 * j) .a3 (N k + 8 * j)) ++
    [.load .d .a7 .a3 (T k + 8 * k), .sub .a7 .a7 .a5] ++ (List.range k).flatMap (selStep k)

/-! ## The sum and the difference -/

/-- `[a3 + T + 8j] := [a] + [b] + a5`, the carry in and out in `a5`. -/
def adcStep (j : Nat) : List Instr :=
  [.load .d .a6 .t4 (8 * j), .load .d .a7 .t5 (8 * j), .add .t0 .a6 .a7, .sltu .t3 .t0 .a7,
    .add .t0 .t0 .a5, .sltu .a1 .t0 .a5, .logic .or .a5 .t3 .a1, .store .d .t0 .a3 (T k + 8 * j)]

/-- `T = [a] + [b]`, `k + 1` words. -/
def addSum : List Instr :=
  [.li .a5 0] ++ (List.range k).flatMap (adcStep k) ++ [.store .d .a5 .a3 (T k + 8 * k)]

/-- Word `j` of `[o] = T + (m and the mask a2)`, the carry in and out in `a5`. -/
def addMStep (j : Nat) : List Instr :=
  [.load .d .a7 .a3 (T k + 8 * j), .load .d .a6 .a3 (N k + 8 * j), .logic .and .a6 .a6 .a2,
    .add .t0 .a7 .a6, .sltu .t3 .t0 .a6, .add .t0 .t0 .a5, .sltu .a1 .t0 .a5, .logic .or .a5 .t3 .a1,
    .store .d .t0 .t2 (8 * j)]

/-- `T = [a] - [b]` with borrows, the mask of the borrow into `a2`, then `m` added
back under it, into `[o]`. -/
def subDiff : List Instr :=
  [.li .a5 0] ++ (List.range k).flatMap (fun j => sbbStep .t4 (8 * j) .t5 (8 * j) .a3 (T k + 8 * j)) ++
    [.li .a2 0, .sub .a2 .a2 .a5, .li .a5 0] ++ (List.range k).flatMap (addMStep k)

/-! ## The operations -/

/-- `[t2] = [t4] [t5] R⁻¹ mod m`. -/
def mulCore : List Instr :=
  fillN k m ++ mulInit k m ++ (List.range k).flatMap (fun i => mulRound k i ++ redRound k) ++ csub k

/-- `[t2] = [t4] + [t5] mod m`. -/
def addCore : List Instr := fillN k m ++ addSum k ++ csub k

/-- `[t2] = [t4] - [t5] mod m`. -/
def subCore : List Instr := fillN k m ++ subDiff k

/-- The element at `a` (from `a3`) as the `8 k` bytes at `p` plus `dst`, a
word at a time. -/
def pack (p : Reg) (a dst : Nat) : List Instr :=
  (List.range (2 * k)).flatMap fun j =>
    [.load .w .a4 .a3 (a + 4 * j)] ++ Words.RISCV64.storeLE32 .a4 .a5 p (dst + 4 * j)

/-- The `8 k` bytes at `p` plus `src` as the element at `o` (from `a3`). -/
def unpack (p : Reg) (o src : Nat) : List Instr :=
  (List.range (2 * k)).flatMap fun j =>
    Words.RISCV64.loadLE32 .a4 .a5 p (src + 4 * j) ++ [.store .w .a4 .a3 (o + 4 * j)]

/-- The operation `core` on operands at any offsets: on the pointers if they
are multiples of 8 (`t0` zero), else on byte-wise copies in the own working
space, the result copied back a byte at a time to `[o]`, kept in `t1`. -/
def fn (core : List Instr) : Prog isa :=
  .seq (.block P256Field.zext) <| .seq (.block ptrs) <|
    .ite (.zero .t0) (.block core)
      (.seq (.block ([.addi .t1 .t2 0] ++ unpack k .t4 (SA k) 0 ++ unpack k .t5 (SB k) 0 ++
          [.addi .t4 .a3 (SA k), .addi .t5 .a3 (SB k), .addi .t2 .a3 (SO k)])) <|
        .seq (.block core) (.block (pack k .t1 (SO k) 0)))

/-- The function multiplying modulo `m`. -/
def mulFn : Prog isa := fn k (mulCore k m)

/-- The function adding modulo `m`. -/
def addFn : Prog isa := fn k (addCore k m)

/-- The function subtracting modulo `m`. -/
def subFn : Prog isa := fn k (subCore k m)

end VG.Impl.Weierstrass.RISCV64.GenWide
