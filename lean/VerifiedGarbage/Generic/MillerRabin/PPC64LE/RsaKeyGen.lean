module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Backend
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Search.Verified
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # The RSA prime search on PPC64LE, its candidates calling each shared Miller–Rabin implementation -/

@[expose] public section

namespace VG.Generic.MillerRabin.PPC64LE.RsaKeyGen

def artifacts (v : Proof.MillerRabin.PPC64LE.RoundImpl) : List Artifact := [
  Spec.RsaKeyGen.primeSearchApi.artifact PPC64LE.target {
    suffix := v.suffix
    stack := 768
    code := Proof.RsaKeyGen.PPC64LE.Search.searchCode v
    verified := Proof.RsaKeyGen.PPC64LE.Search.search_verified v
    features := v.features }]

end VG.Generic.MillerRabin.PPC64LE.RsaKeyGen
