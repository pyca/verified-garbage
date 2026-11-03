module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P256Field
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

For aligned offsets (`mulFnA`), the multiplication builds the constants of
the reduction once rather than in each round (`mulCoreR`): the quotient
constant and `m`'s words in `s2`–`s6`, which it keeps in its own working
space and loads back.

The functions are otherwise as P-256's: constant time, caller-saved
registers only (but `s2`–`s6`, as they were on return), and writes only to
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

/-! ## The multiplication for aligned offsets, with the modulus in registers

`mulCoreR` is `mulCore` with its reduction (`reduceR`) reading the quotient
constant from `s2` and `m`'s words from `s3`–`s6` (`MR`), which it builds
once (`constsR`) rather than in each round: it keeps `s2`–`s6` in the
copies' first five doublewords (from `MA`, free once the product is at
`ACC`) and loads them back after the rounds. -/

/-- The register of `m`'s word `j`. -/
def MR (j : Nat) : Reg := [.s3, .s4, .s5, .s6].getD j .s3

/-- The registers of the constants: `s2`, then `MR 0`–`MR 3`. -/
def KR : List Reg := [.s2, .s3, .s4, .s5, .s6]

/-- `s2`–`s6` to `[a3 + MA]`. -/
def saveM : List Instr := (List.range 5).flatMap fun j => [.store .d (KR.getD j .s2) .a3 (MA + 8 * j)]

/-- `s2`–`s6` from `[a3 + MA]`. -/
def restoreM : List Instr := (List.range 5).flatMap fun j => [.load .d (KR.getD j .s2) .a3 (MA + 8 * j)]

/-- The quotient constant to `s2`, `m`'s words to `s3`–`s6`. -/
def constsR : List Instr :=
  li64 .s2 .a0 (BitVec.ofNat 64 (negInv m)) ++ (List.range 4).flatMap fun j => li64 (MR j) .a0 (wordOf m j)

/-- `qword` with the constants in registers. -/
def qwordR (i : Nat) : List Instr :=
  [.mul (rw i) (rw i) .s2, .mulhu .a4 (rw i) (MR 0), .li .a0 0, .sltu .a0 .a0 (rw i), .add .a4 .a4 .a0]

/-- `mac` with `m`'s word `j` in `MR j`. -/
def macR (i j : Nat) : List Instr :=
  mulWide .a5 .a6 (rw i) (MR j) ++
  [.add .a5 .a5 .a4, .sltu .a7 .a5 .a4, .add .a6 .a6 .a7,
    .add (rw (i + j)) (rw (i + j)) .a5, .sltu .a7 (rw (i + j)) .a5, .add .a4 .a6 .a7]

/-- `round` with the constants in registers. -/
def roundR (i : Nat) : List Instr :=
  [.load .d (rw (i + 4)) .a3 (ACC + 8 * (i + 4))] ++ qwordR i ++ macR i 1 ++ macR i 2 ++ macR i 3 ++
    top (rw (i + 4))

/-- `reduce` with the constants in registers: `s2`–`s6` kept, the
constants, the rounds, and `s2`–`s6` back. -/
def reduceR : List Instr :=
  saveM ++ (constsR m ++ ((List.range 4).map (fun j => .load .d (rw j) .a3 (ACC + 8 * j)) ++ [.li .a2 0] ++
    (List.range 4).flatMap roundR ++ restoreM))

/-- `[t2] = [t4] [t5] R⁻¹ mod m`, with the constants in registers. -/
def mulCoreR : Prog isa := mulWith (reduceR m) (sumC m)

/-- The function multiplying modulo `m`, for aligned offsets. -/
def mulFnA : Prog isa := fnA (mulCoreR m)

/-- The function adding modulo `m`, for aligned offsets. -/
def addFnA : Prog isa := fnA (.block (addCore m))

/-- The function subtracting modulo `m`, for aligned offsets. -/
def subFnA : Prog isa := fnA (.block (subCore m))

end VG.Impl.Weierstrass.RISCV64.Gen4
