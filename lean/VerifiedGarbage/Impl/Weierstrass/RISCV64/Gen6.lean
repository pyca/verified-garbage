module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P384Field
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Gen4
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Rows
public import VerifiedGarbage.Impl.Words.RISCV64.Word64
public import VerifiedGarbage.Impl.Words.RISCV64.Wide

/-!
# Arithmetic modulo any odd six-word modulus, as functions, on RISC-V

`vg_<name>_{mul,add,sub}_mod_<m>(ws, o, a, b)` (`Proof/Weierstrass/MontContract.lean`)
for an odd modulus `m < 2³⁸⁴` known when the code is generated, with the entry,
operands, products, sums and differences of P-384's field
(`Impl/Weierstrass/RISCV64/P384Field.lean`), as the four-word functions
(`Impl/Weierstrass/RISCV64/Gen4.lean`) have P-256's: only the reduction, the
words of `2³⁸⁴ - m` and the words of `m` under a mask use `m`, whose words are
built by `li64` where they are used.

* Montgomery's reduction (`reduce`) keeps six words of the running value in
  registers, `gw i` to `gw (i + 5)` before round `i`. Round `i` takes the
  quotient word `q = w m' mod 2⁶⁴` (`m' = -m⁻¹ mod 2⁶⁴`) of the low word `w`
  into `gw i` and adds `q m` with the low word dropped, as the four-word
  rounds do: only the high word of `q m₀` is needed, with the carry
  `q ≠ 0` (`qword`), and each of `q m₁`–`q m₅` is `mul` and `mulhu`, added
  with its carries (`mac`). Then word `i + 6` of the product is loaded into
  `gw i`, which the quotient no longer needs, and the round's carry word and
  the carry of the round before go into it (Gen4's `top`). A round
  multiplies twelve times.
* The sum: P-384's `sumWith`, with the words of `2³⁸⁴ - m` (`sumKs`).
* The difference: P-384's `subWith`, with `m`'s words under the mask of the
  borrow (`subKs`).

For aligned offsets (`mulFnA`), the multiplication is by rows, in registers
(`Impl/Weierstrass/RISCV64/Rows.lean`).

The functions are otherwise as P-384's: constant time, caller-saved
registers only (but `s6`–`s11`, as they were on return), and writes only to
`[o]` and their own working space.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64.Gen6

open VG.RISCV64
open VG.Impl.Weierstrass.RISCV64.P384Field
open VG.Impl.Weierstrass.RISCV64.Gen4 (wordOf negInv top)
open VG.Impl.Words.RISCV64 (li64 mulWide)

/-- The registers of the reduction's six words, from word `i` at `gw i`:
P-384's `X 0`–`X 4`, then `a0`. -/
def GW : List Reg := [.t5, .t6, .t3, .t4, .a1, .a0]

/-- The register of word `i` of the reduction. -/
def gw (i : Nat) : Reg := GW.getD (i % 6) .t5

variable (m : Nat)

/-! ## Montgomery's reduction -/

/-- The quotient word `q = w m'` of `w` in `gw i`, in place, and in `a4` the
high word of `q m₀` plus `q ≠ 0`, through `t0` and `a5`. -/
def qword (i : Nat) : List Instr :=
  li64 .t0 .a5 (BitVec.ofNat 64 (negInv m)) ++ [.mul (gw i) (gw i) .t0] ++
  li64 .a4 .a5 (wordOf m 0) ++ [.mulhu .a4 (gw i) .a4] ++
  [.li .a5 0, .sltu .a5 .a5 (gw i), .add .a4 .a4 .a5]

/-- `gw (i + j) += q mⱼ + c`, for `q` in `gw i` and the carry word `c` in
`a4`, in and out, through `a5`–`a7`. -/
def mac (i j : Nat) : List Instr :=
  li64 .a6 .a7 (wordOf m j) ++ mulWide .a5 .a6 (gw i) .a6 ++
  [.add .a5 .a5 .a4, .sltu .a7 .a5 .a4, .add .a6 .a6 .a7,
    .add (gw (i + j)) (gw (i + j)) .a5, .sltu .a7 (gw (i + j)) .a5, .add .a4 .a6 .a7]

/-- Round `i`: the quotient word, `q m` added into `gw (i + 1)`–`gw (i + 5)`,
then word `i + 6` of the product loaded into `gw i` and the carry word and
the carry `a2` of the round before added into it, its carries into `a2`. -/
def round (i : Nat) : List Instr :=
  qword m i ++ mac m i 1 ++ mac m i 2 ++ mac m i 3 ++ mac m i 4 ++ mac m i 5 ++
    [.load .d (gw i) .a3 (ACC + 8 * (i + 6))] ++ top (gw i)

/-- The product at `ACC` reduced: its low six words loaded, the carry zero,
the six rounds, and the top word moved from `a0` to `X 5`. -/
def reduce : List Instr :=
  (List.range 6).map (fun j => .load .d (gw j) .a3 (ACC + 8 * j)) ++ [.li .a2 0] ++
    (List.range 6).flatMap (round m) ++ [.addi .a4 .a0 0]

/-! ## The sum and the difference -/

/-- The words of `2³⁸⁴ - m` into `t0`, through `a6`. -/
def sumKs : List (List Instr) :=
  (List.range 6).map fun j => li64 .t0 .a6 (wordOf (2 ^ 384 - m) j)

/-- `m`'s words under the mask in `t0`, into `a6`, through `a0`. -/
def subKs : List (List Instr) :=
  (List.range 6).map fun j => li64 .a6 .a0 (wordOf m j) ++ [.logic .and .a6 .a6 .t0]

/-! ## The operations -/

/-- `[t2] = [t4] [t5] R⁻¹ mod m`. -/
def mulCore : Prog isa := mulWith (reduce m) (sumWith (sumKs m))

/-- `[t2] = [t4] + [t5] mod m`. -/
def addCore : List Instr := addSum ++ (sumWith (sumKs m) ++ csubTail)

/-- `[t2] = [t4] - [t5] mod m`. -/
def subCore : List Instr := subWith (subKs m)

/-- The function multiplying modulo `m`. -/
def mulFn : Prog isa := fn (mulCore m)

/-- The function adding modulo `m`. -/
def addFn : Prog isa := fn (.block (addCore m))

/-- The function subtracting modulo `m`. -/
def subFn : Prog isa := fn (.block (subCore m))

/-! ## The multiplication for aligned offsets, by rows in registers -/

/-- The registers, and where in the own working space those kept and the product are. -/
def lay : Rows.Lay where
  k := 6
  VL := [.t0, .t1, .a7, .s7, .s8, .s9]
  AL := [.a0, .a1, .a2, .a4, .a5, .a6]
  LO := [.t6, .s6, .s10]
  HI := [.s11]
  KR := [.s6, .s7, .s8, .s9, .s10, .s11, .t1]
  sv := 1664
  pp := 1760

/-- The order of the code, found by timing orders on T-Head's C910. -/
def order : Rows.Order where
  mul := [
    0, 1, 2, 2, 0, 0, 0, 2, 1, 2, 1, 8, 1, 1, 10, 1, 2, 1, 11, 1, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 4, 0, 0, 0, 1,
    2, 12, 5, 2, 17, 40, 11, 0, 10, 0, 0, 13, 0, 0, 11, 0, 1, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 11, 0, 11, 0, 0, 0, 8, 1,
    0, 0, 0, 0, 0, 0, 0, 5, 1, 4, 5, 23, 46, 0, 0, 0, 0, 11, 4, 1, 0, 16, 9, 15, 0, 0, 0, 6, 0, 0, 0, 0, 0, 2, 0, 0,
    7, 8, 0, 0, 2, 0, 0, 0, 7, 2, 0, 6, 0, 5, 1, 0, 0, 0, 0, 5, 1, 25, 4, 0, 4, 0, 0, 12, 0, 0, 0, 17, 2, 0, 36, 15,
    0, 0, 0, 5, 1, 0, 0, 0, 1, 0, 1, 8, 0, 0, 0, 0, 5, 1, 0, 0, 2, 6, 0, 6, 0, 5, 0, 0, 0, 0, 0, 5, 1, 4, 0, 0, 3,
    21, 0, 2, 42, 0, 0, 9, 0, 16, 16, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1, 8, 0, 0, 0, 2, 11, 5, 5, 0, 9, 0, 0, 0, 2,
    0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 13, 0, 1, 18, 12, 18, 1, 0, 0, 0, 1, 7, 1, 0, 0, 30, 0, 0, 0, 28, 11, 0, 1,
    10, 0, 0, 2, 0, 6, 2, 18, 9, 0, 16, 0, 8, 0, 0, 2, 5, 10, 0, 0, 0, 0, 0, 1, 4]
  sqr := [
    1, 0, 0, 4, 0, 8, 0, 2, 0, 2, 1, 12, 0, 6, 0, 0, 1, 0, 0, 10, 10, 0, 22, 1, 1, 0, 0, 0, 0, 23, 0, 16, 16, 0, 7,
    1, 0, 17, 17, 1, 1, 0, 19, 0, 0, 0, 0, 1, 14, 0, 0, 0, 2, 0, 0, 8, 0, 0, 0, 6, 6, 24, 1, 0, 0, 0, 11, 0, 3, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1, 0, 6, 31, 6, 0, 31, 1, 0, 0, 0, 2, 0, 0, 11, 0, 2, 0, 0, 19, 0, 39, 0, 1, 0, 3, 0, 0, 1,
    0, 0, 0, 0, 2, 16, 0, 0, 1, 0, 0, 1, 1, 18, 0, 0, 0, 0, 5, 5, 0, 0, 0, 2, 0, 1, 1, 1, 4, 0, 2, 0, 20, 1, 0, 8, 0,
    16, 0, 6, 0, 0, 4, 4, 0, 0, 0, 7, 1, 0, 5, 0, 0, 3, 2, 0, 0, 18, 7, 0, 6, 0, 0, 0, 3, 3, 3, 0, 1, 1, 0, 0, 3, 0,
    1, 21, 1, 0, 0, 0, 7, 16, 0, 0, 5, 0, 0, 2, 2, 0, 0, 0, 0, 0, 4, 4, 0, 2, 0, 20, 0, 0, 0, 6, 15, 0, 5, 0, 4, 0,
    0, 2, 2, 0, 6, 1, 1, 0, 2, 0, 1, 1, 0, 7, 0, 0, 5, 0, 4, 0, 0, 1, 1, 1, 0, 0, 0, 2]
  tail := [
    0, 17, 34, 0, 16, 1, 0, 36, 0, 37, 34, 0, 13, 12, 0, 11, 2, 10, 27, 22, 2, 22, 6, 20, 20, 20, 25, 0, 2, 0, 20,
    20, 0, 2, 16, 6, 0, 0, 6, 6, 0, 11, 9, 3, 9, 9, 0, 9, 0, 0, 6, 2, 0, 0, 3, 0, 2, 5, 2, 2, 2, 0, 1, 1, 0, 5, 0, 0,
    0, 3, 8, 0, 28, 0, 0, 0, 11, 0, 4, 0, 0, 0, 7, 0, 6, 0, 1, 0, 0, 32, 0, 0, 0, 30, 0, 2, 0, 0, 26, 0, 0, 15, 8, 0,
    0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 5, 1, 0, 0, 0, 10, 0, 30, 1, 0, 0, 0, 2, 5, 0, 4, 0, 0, 6, 0, 0, 5, 1, 4, 34, 0,
    0, 33, 0, 2, 0, 0, 0, 0, 0, 26, 10, 0, 0, 14, 0, 2, 0, 0, 11, 0, 0, 9, 0, 0, 0, 0, 1, 0, 0, 0, 0, 9, 30, 1, 0, 0,
    0, 0, 5, 0, 0, 8, 0, 2, 0, 0, 1, 4, 35, 0, 3, 0, 0, 0, 4, 1, 0, 0, 0, 10, 25, 16, 0, 0, 3, 0, 0, 12, 0, 0, 0, 15,
    0, 0, 0, 6, 0, 1, 0, 0, 0, 0, 9, 30, 1, 0, 0, 0, 0, 1, 0, 0, 2, 7, 2, 7, 0, 2, 0, 0, 0, 0, 32, 1, 0, 0, 0, 29, 0,
    1, 0, 0, 0, 0, 14, 2, 0, 0, 0, 3, 10, 0, 0, 0, 0, 12, 0, 5, 1, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 1, 0, 0, 2, 7, 20,
    0, 0, 0, 5, 0, 0, 0, 0, 32, 1, 32, 0, 1, 0, 0, 0, 0, 26, 0, 16, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0,
    0, 0, 10, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 6, 0, 0, 1, 0, 0, 0, 1, 0, 0, 4, 0, 0, 18, 0, 0, 0, 10, 0, 0, 8, 0, 0,
    1, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 4, 0, 3, 0, 0, 4, 0, 0, 0, 0, 9, 0, 0, 14, 0, 16, 0, 0, 0, 10, 0, 2,
    10, 0, 0, 0, 1, 4, 1, 0, 0, 4, 0, 0, 0, 1]

/-- The function multiplying modulo `m`, for aligned offsets. -/
def mulFnA : Prog isa := fnA (Rows.fast lay m order)

/-- The function adding modulo `m`, for aligned offsets. -/
def addFnA : Prog isa := fnA (.block (addCore m))

/-- The function subtracting modulo `m`, for aligned offsets. -/
def subFnA : Prog isa := fnA (.block (subCore m))

end VG.Impl.Weierstrass.RISCV64.Gen6
