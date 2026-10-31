module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Instances
public import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA parameter generation on PPC64LE, calling the probable-prime tests over each Miller–Rabin round -/

@[expose] public section

namespace VG.Generic.MillerRabin.PPC64LE.DsaParameters
open VG Proof.Dsa.PPC64LE.Gen

def artifacts (v : Proof.MillerRabin.PPC64LE.RoundImpl) : List Artifact := [
  Spec.Dsa.generateParametersApi.artifact PPC64LE.target {
    suffix := v.suffix
    code := Impl.Dsa.PPC64LE.Generation.code (gen1 v) (gen2 v) (gen3 v)
    stack := 176
    consts := Impl.RsaKeyGen.TrialTable32.consts
    verified := generate_params v
    features := v.features }]

end VG.Generic.MillerRabin.PPC64LE.DsaParameters
