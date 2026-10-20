module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrograms
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateVerified
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedPrepareAtCT
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailInstance

/-! # Key-generation instances follow every callable Montgomery variant -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeyGenerate
open VG VG.Arm VG.Proof.Bignum.Arm

def backend (b : MontBackend) : KeyBackend where
  generateKey := code b
  generateKey_verified := keyGenerate_verified (prepare b) (tail b)
    (sharedPrepareLaw b) (tailLaw b)
  keyStack := stack_ok b
  suffix := b.suffix
  features := b.features

end VG.Proof.Ffdh.Arm.KeyGenerate
