module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Verified
public import VerifiedGarbage.Spec.Ffdh.SievedContract

/-! # Emit complete native FFDH parameter generation for every shared ARMv7 Miller–Rabin backend -/

@[expose] public section
namespace VG.Generic.MillerRabin.Arm.Ffdh
open VG

def artifacts (v : Proof.MillerRabin.Arm.RoundImpl) : List Artifact :=
  let b := Proof.Ffdh.Arm.parameterBackend v
  [Spec.Ffdh.sievedParameterSearchApi.artifact VG.Arm.target {
    suffix := b.suffix
    features := b.features
    stack := 232
    code := Impl.Ffdh.Arm.ParameterSearch.code (.call b.candidateName b.candidate)
    verified := Proof.Ffdh.Arm.ParameterSearch.verified b }]

end VG.Generic.MillerRabin.Arm.Ffdh
