module

public import VerifiedGarbage.Impl.Bignum.Arm.MaskBytes

/-! # Mask an RSA output using the secret acceptance bit saved in the frame

r4 is the output, r6 its length. Frame slot 48 holds 0 or 1. Return that
bit in r0, and replace every output byte with zero when the bit is zero.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def maskOutputArgs : List Instr :=
  [.mov .r0 (.reg .r4), .mov .lr (.reg .r6), .ldrSp .r4 48,
   .mov .r2 (.imm 0), .dp .sub .r2 .r2 (.reg .r4)]

def maskOutput : Prog isa :=
  .seq (.block maskOutputArgs) (.seq maskBytes (.block [.mov .r0 (.reg .r4)]))

end VG.Impl.Bignum.Arm
