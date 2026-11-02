module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # FFDH parameter generation calls each shared Miller–Rabin implementation -/

@[expose] public section

namespace VG.Generic.MillerRabin.PPC64LE.Ffdh

def artifacts (v : Proof.MillerRabin.PPC64LE.RoundImpl) : List Artifact := [
  Spec.Ffdh.parameterSearchApi.artifact PPC64LE.target {
    suffix := v.suffix
    stack := 336
    code := Proof.Ffdh.PPC64LE.Generation.searchCode v
    verified := Proof.Ffdh.PPC64LE.Generation.search_verified v
    features := v.features }]

end VG.Generic.MillerRabin.PPC64LE.Ffdh
