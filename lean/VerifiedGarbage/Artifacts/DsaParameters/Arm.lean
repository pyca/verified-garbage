module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Instances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Variants.MillerRabin.Arm

/-! # DSA parameter generation over refillable tapes on ARMv7, calling the probable-prime test over each Miller–Rabin round -/

@[expose] public section

namespace VG.Artifacts.DsaParameters.Arm
open VG Proof.Dsa.Arm.Gen

def artifactsFor (v : Proof.MillerRabin.Arm.RoundImpl) : List Artifact := [
  Spec.Dsa.parameterSearchApi.artifact Arm.target {
    suffix := v.suffix
    code := Impl.Dsa.Arm.Generation.code (geo1 v) (geo2 v) (geo3 v)
    stack := 304
    verified := search_params v
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.MillerRabin.Arm.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.DsaParameters.Arm
