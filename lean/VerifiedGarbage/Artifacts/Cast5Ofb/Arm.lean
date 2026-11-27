module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cast5.Ofb
public import VerifiedGarbage.Spec.Cast5.OfbFinal
import VerifiedGarbage.Proof.Cast5.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # CAST5-OFB on ARMv7 -/

namespace VG.Artifacts.Cast5Ofb.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Cast5.ofbApi.artifact Arm.target {
    code := Impl.Cast5.Arm.Fn.ofb
    verified := Proof.Cast5.Arm.Fn.ofb },
  Spec.Cast5.ofbFinalApi.artifact Arm.target {
    code := Impl.Cast5.Arm.Fn.ofbFinal
    verified := Proof.Cast5.Arm.Fn.ofbFinal }]

spec_apis artifacts

end VG.Artifacts.Cast5Ofb.Arm
