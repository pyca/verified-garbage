module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P256Field
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Rows
public import VerifiedGarbage.Impl.Words.RISCV64.Word64
public import VerifiedGarbage.Impl.Words.RISCV64.Wide

/-!
# Arithmetic modulo any odd four-word modulus, as functions, on RISC-V

`vg_<name>_{mul,add,sub}_mod_<m>(ws, o, a, b)` (`Proof/Weierstrass/MontContract.lean`)
for an odd modulus `m < 2²⁵⁶` known when the code is generated, with the entry,
operands, products, sums and differences of P-256's field
(`Impl/Weierstrass/RISCV64/P256Field.lean`); only the reduction, the final
subtraction and the modulus's words under a mask use `m`, whose words are
built by `li64` where they are used:

* Montgomery's reduction (`reduce`): round `i` takes the quotient word
  `q = w m' mod 2⁶⁴` (`m' = -m⁻¹ mod 2⁶⁴`) of the low word `w`, and adds
  `q m` with the low word dropped: the low word of `w + q m₀` is zero and its
  carry is `q ≠ 0` (`w` is zero if and only if `q` is), so only the high word
  of `q m₀` is needed (`mulhu`), and each of `q m₁`, `q m₂`, `q m₃` is `mul`
  and `mulhu`, added with its carries (`mac`); the round's carry out is the
  two carries of its top word's two additions. A round multiplies eight
  times.
* `csub`: `x + (2²⁵⁶ - m)`, then P-256's `csubTail`.
* `subCore`: `m`'s words under the mask of the borrow, each `li64` and `and`.

For aligned offsets (`mulFnA`), the multiplication is by rows, in registers
(`Impl/Weierstrass/RISCV64/Rows.lean`).

The functions are otherwise as P-256's: constant time, caller-saved
registers only (but `s7`–`s11`, as they were on return), and writes only to
`[o]` and their own working space.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64.Gen4

open VG.RISCV64
open VG.Impl.Weierstrass.RISCV64.P256Field
open VG.Impl.Words.RISCV64 (li64 mulWide)

/-- Word `j` of `x`. -/
def wordOf (x j : Nat) : BitVec 64 := BitVec.ofNat 64 (x >>> (64 * j))

/-- `-x⁻¹ mod 2⁶⁴` for an odd `x`, by Newton's iteration from `x` (correct
to three bits), each step doubling the correct bits. -/
def negInv (x : Nat) : Nat :=
  let step := fun (y : Nat) => y * (2 + 2 ^ 64 - x * y % 2 ^ 64) % 2 ^ 64
  (2 ^ 64 - step (step (step (step (step x % 2 ^ 64))))) % 2 ^ 64

variable (m : Nat)

/-! ## Montgomery's reduction -/

/-- The quotient word `q = w m'` of `w` in `rw i`, in place, and in `a4` the
high word of `q m₀` plus `q ≠ 0`. -/
def qword (i : Nat) : List Instr :=
  li64 .t0 .a0 (BitVec.ofNat 64 (negInv m)) ++ [.mul (rw i) (rw i) .t0] ++
  li64 .a4 .a0 (wordOf m 0) ++ [.mulhu .a4 (rw i) .a4] ++
  [.li .a0 0, .sltu .a0 .a0 (rw i), .add .a4 .a4 .a0]

/-- `rw (i + j) += q mⱼ + c`, for `q` in `rw i` and the carry word `c` in
`a4`, in and out, through `a5`–`a7` and `a0`. -/
def mac (i j : Nat) : List Instr :=
  li64 .a6 .a0 (wordOf m j) ++ mulWide .a5 .a6 (rw i) .a6 ++
  [.add .a5 .a5 .a4, .sltu .a7 .a5 .a4, .add .a6 .a6 .a7,
    .add (rw (i + j)) (rw (i + j)) .a5, .sltu .a7 (rw (i + j)) .a5, .add .a4 .a6 .a7]

/-- The carry word `a4` and the carry `a2` of the round before into `d`,
their carries into `a2`. -/
def top (d : Reg) : List Instr :=
  [.add d d .a4, .sltu .a7 d .a4, .add d d .a2, .sltu .a2 d .a2, .add .a2 .a2 .a7]

/-- Round `i`: word `i + 4` of the product loaded, the quotient word, `q m`
added into `rw (i + 1)`–`rw (i + 3)`, then the carry word and the carry `a2`
of the round before into `rw (i + 4)`, its carries into `a2`. -/
def round (i : Nat) : List Instr :=
  [.load .d (rw (i + 4)) .a3 (ACC + 8 * (i + 4))] ++ qword m i ++ mac m i 1 ++ mac m i 2 ++ mac m i 3 ++
    top (rw (i + 4))

/-- The product at `ACC` reduced, as P-256's `reduce`. -/
def reduce : List Instr :=
  (List.range 4).map (fun j => .load .d (rw j) .a3 (ACC + 8 * j)) ++ [.li .a2 0] ++
    (List.range 4).flatMap (round m)

/-! ## The final subtraction -/

/-- `x + (2²⁵⁶ - m)` into `t6`, `a4`–`a6`, its carry into `a7`. -/
def sumC : List Instr :=
  li64 .t0 .a0 (wordOf (2 ^ 256 - m) 0) ++ [.add .t6 X0 .t0, .sltu .a7 .t6 .t0] ++
  li64 .t0 .a0 (wordOf (2 ^ 256 - m) 1) ++ csubWord .a4 X1 ++
  li64 .t0 .a0 (wordOf (2 ^ 256 - m) 2) ++ csubWord .a5 X2 ++
  li64 .t0 .a0 (wordOf (2 ^ 256 - m) 3) ++ csubWord .a6 X3

/-! ## The operations -/

/-- Word `j` of `m` under the mask in `t0`, into `t6`. -/
def kword (j : Nat) : List Instr := li64 .t6 .a0 (wordOf m j) ++ [.logic .and .t6 .t6 .t0]

/-- `[t2] = [t4] [t5] R⁻¹ mod m`. -/
def mulCore : Prog isa := mulWith (reduce m) (sumC m)

/-- `[t2] = [t4] + [t5] mod m`. -/
def addCore : List Instr := addSum ++ (sumC m ++ csubTail)

/-- `[t2] = [t4] - [t5] mod m`. -/
def subCore : List Instr := subWith (kword m 0) (kword m 1) (kword m 2) (kword m 3)

/-- The function multiplying modulo `m`. -/
def mulFn : Prog isa := fn (mulCore m)

/-- The function adding modulo `m`. -/
def addFn : Prog isa := fn (.block (addCore m))

/-- The function subtracting modulo `m`. -/
def subFn : Prog isa := fn (.block (subCore m))

/-! ## The multiplication for aligned offsets, by rows in registers -/

/-- The registers, and where in the own working space those kept and the product are. -/
def lay : Rows.Lay where
  k := 4
  VL := [.t0, .a7, .a5, .a6]
  AL := [.a0, .a1, .a2, .a4]
  LO := [.t6, .s11, .s7, .s8]
  HI := [.s9, .s10]
  KR := [.s11, .s7, .s8, .s9, .s10]
  sv := 1792
  pp := 1856

/-- The order of the code, found by timing orders on T-Head's C910. -/
def order : Rows.Order where
  mul := [
    3, 1, 0, 0, 0, 2, 1, 2, 2, 1, 0, 0, 0, 9, 5, 0, 3, 0, 0, 5, 5, 0, 17, 16, 0, 0, 3, 0, 0, 1, 10, 15, 0, 15, 20, 0,
    14, 0, 1, 1, 0, 4, 1, 0, 2, 0, 0, 0, 2, 0, 0, 5, 1, 4, 0, 0, 14, 0, 6, 2, 2, 0, 10, 0, 22, 0, 8, 0, 11, 0, 5, 10,
    0, 0, 0, 0, 1, 0, 0, 3, 2, 7, 0, 1, 5, 0, 16, 0, 0, 0, 6, 19, 0, 19, 0, 0, 0, 21, 0, 8, 0, 6, 6, 11, 6, 0, 0, 0,
    0, 0, 0, 3, 0, 7, 7, 0, 1, 0, 0, 0, 2]
  sqr := [
    2, 0, 4, 0, 0, 6, 1, 2, 1, 0, 2, 33, 0, 0, 6, 0, 0, 5, 2, 0, 0, 1, 4, 1, 0, 0, 0, 7, 0, 0, 1, 0, 0, 2, 13, 0, 0,
    0, 21, 1, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 6, 6, 0, 0, 0, 3, 3, 0, 2, 1, 0, 6, 0, 2, 2, 3, 0, 0, 9, 0,
    0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 9, 0, 0, 5, 6, 0, 0, 0, 1, 0, 1, 8, 0, 0, 0, 5, 0, 0, 0, 1, 1, 1, 1, 0, 0, 6, 4, 0,
    2, 0, 11, 2, 0, 0, 0, 0, 0, 5, 0, 0, 3, 3, 2, 2, 2]
  tail := [
    6, 3, 0, 0, 26, 20, 20, 0, 0, 0, 23, 18, 21, 18, 17, 17, 19, 17, 0, 0, 0, 0, 1, 14, 1, 1, 0, 0, 9, 0, 1, 7, 9, 3,
    0, 13, 5, 2, 0, 3, 0, 8, 1, 1, 1, 5, 2, 4, 0, 0, 0, 5, 0, 0, 16, 3, 0, 0, 7, 1, 1, 0, 1, 0, 0, 0, 10, 0, 0, 14,
    0, 0, 0, 1, 0, 9, 0, 8, 0, 0, 11, 0, 0, 0, 3, 3, 0, 0, 0, 3, 3, 14, 0, 0, 6, 1, 0, 1, 0, 0, 0, 18, 0, 16, 0, 8,
    0, 0, 0, 1, 16, 0, 9, 0, 8, 0, 0, 0, 5, 0, 0, 7, 7, 0, 0, 0, 3, 13, 7, 0, 2, 0, 0, 20, 0, 19, 0, 0, 0, 9, 0, 0,
    19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 2, 0, 0, 0, 1, 0, 3, 2, 6, 2, 0, 0, 14, 0, 0, 0, 15, 0, 0, 3, 0, 7, 10,
    0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 7, 3, 0, 0, 7, 0, 0, 0, 0, 0, 0, 1, 0, 2]

/-- The function multiplying modulo `m`, for aligned offsets. -/
def mulFnA : Prog isa := fnA (Rows.fast lay m order)

/-- The function adding modulo `m`, for aligned offsets. -/
def addFnA : Prog isa := fnA (.block (addCore m))

/-- The function subtracting modulo `m`, for aligned offsets. -/
def subFnA : Prog isa := fnA (.block (subCore m))

end VG.Impl.Weierstrass.RISCV64.Gen4
