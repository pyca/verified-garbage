module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Ofb
public import VerifiedGarbage.Spec.Idea.OfbFinal
import VerifiedGarbage.Proof.Idea.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA-OFB on ARMv7 -/

namespace VG.Artifacts.IdeaOfb.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Idea.ofbApi.artifact Arm.target {
    code := Impl.Idea.Arm.Fn.ofb
    verified := Proof.Idea.Arm.Fn.ofb },
  Spec.Idea.ofbFinalApi.artifact Arm.target {
    code := Impl.Idea.Arm.Fn.ofbFinal
    verified := Proof.Idea.Arm.Fn.ofbFinal }]

spec_apis artifacts

end VG.Artifacts.IdeaOfb.Arm
