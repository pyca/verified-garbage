module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Instances
public import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA parameter generation on ARMv7, calling the probable-prime test over each Miller–Rabin round -/

@[expose] public section

namespace VG.Generic.MillerRabin.Arm.DsaParameters
open VG Proof.Dsa.Arm.Gen

def artifacts (v : Proof.MillerRabin.Arm.RoundImpl) : List Artifact := [
  Spec.Dsa.generateParametersApi.artifact Arm.target {
    suffix := v.suffix
    code := Impl.Dsa.Arm.Generation.code (geo1 v) (geo2 v) (geo3 v)
    stack := 304
    verified := params_verified v
    features := v.features }]

end VG.Generic.MillerRabin.Arm.DsaParameters
