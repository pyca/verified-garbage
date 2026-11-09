module

public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAt
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyCallMemory
public import VerifiedGarbage.Proof.Framework.RelCT

/-! # Modulus preparation shared by key-generation arithmetic backends

The public modulus gate supplies the lower bound for its packed-word width.
Preparation may use that normalization without adding a caller obligation to
FFDH's shared contract.
-/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

def keyPrepareWrites (p : Inputs) (s : State) : List Region :=
  prepareAtWrites p s ++ [FrameStack.belowA s.sp 48]

end VG.Proof.Ffdh.Arm
