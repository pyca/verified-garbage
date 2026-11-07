module

public import VerifiedGarbage.Proof.MillerRabin.X86.Backend
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Generate.Verified
public import VerifiedGarbage.TCB.X86.Print

/-! # RSA key generation on i686, its prime searches' candidates calling each shared Miller–Rabin implementation -/

@[expose] public section
namespace VG.Generic.MillerRabin.X86.RsaKeyGen
open VG VG.X86 VG.Proof.MillerRabin.X86

def artifacts (v : RoundImpl) : List Artifact := [
  Spec.RsaKeyGen.keySearchApi.artifact target {
    suffix := v.suffix
    code := Proof.RsaKeyGen.X86.Generate.genCode v
    stack := 284
    verified := Proof.RsaKeyGen.X86.Generate.gen_verified v
    spSafe := Proof.RsaKeyGen.X86.Generate.genCode_sp v
    features := v.features }]

end VG.Generic.MillerRabin.X86.RsaKeyGen
