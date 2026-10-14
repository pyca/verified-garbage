module

public import VerifiedGarbage.Impl.Bignum.Arm.Zero
public import VerifiedGarbage.Impl.Bignum.Arm.ReverseBytes

/-! # Zero-extended import of runtime-sized RSA integers

r0/r5 name the destination, lr counts its 32-bit limbs, and r3 is zero.
r4 names the source and r6 counts its nonzero number of big-endian bytes.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def loadBEreverseArgs : List Instr :=
  [.mov .r0 (.reg .r5), .dp .add .r1 .r4 (.reg .r6),
   .dp .sub .r1 .r1 (.imm 1), .mov .lr (.reg .r6)]

def loadBE : Prog isa := .seq zero (.seq (.block loadBEreverseArgs) reverseBytes)

end VG.Impl.Bignum.Arm
