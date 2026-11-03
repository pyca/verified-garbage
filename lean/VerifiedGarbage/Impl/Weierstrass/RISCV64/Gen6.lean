module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P384Field
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Gen4
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

The functions are otherwise as P-384's: constant time, caller-saved
registers only, and writes only to `[o]` and their own working space.
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

/-- The function multiplying modulo `m`, for aligned offsets. -/
def mulFnA : Prog isa := fnA (mulCore m)

/-- The function adding modulo `m`, for aligned offsets. -/
def addFnA : Prog isa := fnA (.block (addCore m))

/-- The function subtracting modulo `m`, for aligned offsets. -/
def subFnA : Prog isa := fnA (.block (subCore m))

end VG.Impl.Weierstrass.RISCV64.Gen6
