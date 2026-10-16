module

public import VerifiedGarbage.Impl.Bignum.Arm.SubRow

/-! # Compare the imported RSA input with the modulus without branching on it -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def inputCompareArgs : List Instr :=
  [.ldr .r10 .r0 72, .ldr .r12 .r0 64, .ldr .lr .r0 48,
   .dp .add .lr .lr (.reg .lr), .ldr .r0 .r0 88, .mov .r11 (.imm 0)]
def inputCompare : Prog isa :=
  .seq (.block inputCompareArgs) (.seq subRow (.block [.ldrSp .r0 0]))

end VG.Impl.Bignum.Arm
