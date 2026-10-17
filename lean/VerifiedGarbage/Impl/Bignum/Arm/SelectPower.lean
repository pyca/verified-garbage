module

public import VerifiedGarbage.Impl.Bignum.Arm.Select

/-! # Select a private-exponent power without secret-dependent control flow -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

/-- Select array 6 or array 1 using the secret bit in r11. -/
def selectPowerArgs : List Instr :=
  [.ldr .r10 .r0 112, .ldr .r12 .r0 72, .ldr .lr .r0 48,
   .dp .add .lr .lr (.reg .lr), .ldr .r0 .r0 112]
def selectPower : Prog isa :=
  .seq (.block selectPowerArgs) (.seq selectRow (.block [.ldrSp .r0 0]))

end VG.Impl.Bignum.Arm
