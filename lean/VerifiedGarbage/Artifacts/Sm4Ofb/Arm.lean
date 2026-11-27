module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Ofb
public import VerifiedGarbage.Spec.Sm4.OfbFinal
import VerifiedGarbage.Proof.Sm4.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-OFB on ARMv7 -/

namespace VG.Artifacts.Sm4Ofb.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Sm4.ofbApi.artifact Arm.target {
    code := Impl.Sm4.Arm.Fn.ofb
    verified := Proof.Sm4.Arm.Fn.ofb },
  Spec.Sm4.ofbFinalApi.artifact Arm.target {
    code := Impl.Sm4.Arm.Fn.ofbFinal
    verified := Proof.Sm4.Arm.Fn.ofbFinal }]

spec_apis artifacts

end VG.Artifacts.Sm4Ofb.Arm
