module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Backend
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Generate.Verified
public import VerifiedGarbage.Proof.Rsa.PPC64LE.Instances
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # RSA key generation on PPC64LE, its prime searches' candidates calling each shared Miller–Rabin implementation -/

@[expose] public section

namespace VG.Generic.MillerRabin.PPC64LE.RsaKeyGen

def artifacts (v : Proof.MillerRabin.PPC64LE.RoundImpl) : List Artifact := [
  Spec.RsaKeyGen.keySearchApi.artifact PPC64LE.target {
    suffix := v.suffix
    stack := 1088
    code := Proof.RsaKeyGen.PPC64LE.Generate.genCode v
    verified := Proof.RsaKeyGen.PPC64LE.Generate.gen_verified v
    features := v.features }]

end VG.Generic.MillerRabin.PPC64LE.RsaKeyGen
