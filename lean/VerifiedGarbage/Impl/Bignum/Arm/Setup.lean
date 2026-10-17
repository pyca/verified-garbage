module

public import VerifiedGarbage.Impl.Bignum.Arm.SetBases

/-! # Initialize the shared RSA workspace layout

r0 is the workspace base, r7 its count of 64-bit limbs, and r3 is zero.
The header stores this count and all eight zero-extended array addresses.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def setupArgs : List Instr :=
  [.mov .r8 (.reg .r0), .dp .add .r5 .r7 (.imm 2), .mov .r5 (.shifted .r5 .lsl 3),
   .dp .add .r4 .r0 (.imm 256), .dp .add .r0 .r0 (.imm 64), .mov .lr (.imm 8)]

def setup : Prog isa := .seq (.block (store64 .r7 .r3 .r0 48))
  (.seq (.block setupArgs) (.seq setBases (.block [.mov .r0 (.reg .r8)])))

end VG.Impl.Bignum.Arm
