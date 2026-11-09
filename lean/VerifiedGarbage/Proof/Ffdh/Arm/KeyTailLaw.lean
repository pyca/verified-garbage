module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTail
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailCT
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyCallMemory
import VerifiedGarbage.Impl.Ffdh.Arm.KeyGenerate

public import VerifiedGarbage.TCB.Arm.Isa

/-! # The public-value exponentiation boundary of a key-generation attempt -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)

def keyCallWrites (p : Inputs) (s : State) : List Region :=
  keyWrites p s ++ [FrameStack.belowA s.sp 48]

end VG.Proof.Ffdh.Arm
