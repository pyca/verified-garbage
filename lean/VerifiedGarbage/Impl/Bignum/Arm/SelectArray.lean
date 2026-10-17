module

public import VerifiedGarbage.Impl.Bignum.Arm.Select

/-! # Select workspace arrays without secret-dependent control flow -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

/-- Select array a or b into o using the secret bit in r11. -/
def selectArrayArgs (o a b : Nat) : List Instr :=
  [.ldr .r10 .r0 (64 + 8 * a), .ldr .r12 .r0 (64 + 8 * b), .ldr .lr .r0 48,
   .dp .add .lr .lr (.reg .lr), .ldr .r0 .r0 (64 + 8 * o)]
def selectArray (o a b : Nat) : Prog isa :=
  .seq (.block (selectArrayArgs o a b)) (.seq selectRow (.block [.ldrSp .r0 0]))

end VG.Impl.Bignum.Arm
