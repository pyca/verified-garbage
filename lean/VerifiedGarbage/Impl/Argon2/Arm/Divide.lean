import VerifiedGarbage.Impl.Argon2.Arm.Layout

/-!
# Fixed-time unsigned division on ARMv7

`r1` holds the numerator and `r2` the positive divisor, below 2³¹. Each of
the 32 bits, from the most significant, takes the same eight instructions:
`adds r1, r1, r1` shifts the next numerator bit out into C (and makes room for
a quotient bit at the bottom of `r1`), `adc` shifts it into the remainder in
`r0`, the divisor is subtracted (`subs`, C if it fits), C is added to `r1` as
the quotient bit, and that bit less one (all ones if the divisor did not
fit), masked with the divisor, adds it back. The quotient ends in `r1` and the remainder in `r0`;
`r3` is a temporary. There are no branches and no memory accesses, so the
numerator may be secret.
-/

namespace VG.Impl.Argon2.Arm.Divide

open VG.Arm

/-- One bit of the division by `r2`. -/
def bit : List Instr :=
  [.adds .r1 .r1 (.reg .r1), .adc .r0 .r0 (.reg .r0), .subs .r0 .r0 (.reg .r2), .adc .r1 .r1 (.imm 0),
    .dp .and .r3 .r1 (.imm 1), .dp .sub .r3 .r3 (.imm 1), .dp .and .r3 .r3 (.reg .r2),
    .dp .add .r0 .r0 (.reg .r3)]

/-- `n` bits. -/
def bits : Nat → List Instr
  | 0 => []
  | n + 1 => bits n ++ bit

def code : List Instr := .mov .r0 (.imm 0) :: bits 32

end VG.Impl.Argon2.Arm.Divide
