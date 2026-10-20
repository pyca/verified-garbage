module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyInitVerified
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterInitVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! Native FFDH on little-endian AAPCS ARMv7, including baseline and UMAAL arithmetic. -/

@[expose] public section
namespace VG.Artifacts.Ffdh.Arm
open VG

def artifacts : List Artifact :=
  [
    Spec.Ffdh.keyInitApi.artifact VG.Arm.target {
      code := Impl.Ffdh.Arm.KeyGeneration.init
      verified := Proof.Ffdh.Arm.keyInit_verified },
    Spec.Ffdh.parameterInitApi.artifact VG.Arm.target {
      code := Impl.Ffdh.Arm.Generation.init
      verified := Proof.Ffdh.Arm.parameterInit_verified }]

end VG.Artifacts.Ffdh.Arm
