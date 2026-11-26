module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Contract
import VerifiedGarbage.Proof.Idea.Arm.Scrub
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA on ARMv7 -/

namespace VG.Artifacts.Idea.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Idea.expandKeyApi.artifact Arm.target {
    code := Impl.Idea.Arm.Fn.expandKey
    verified := Proof.Idea.Arm.Fn.expandKey },
  Spec.Idea.invertKeyApi.artifact Arm.target {
    code := Impl.Idea.Arm.Fn.invertKey
    verified := Proof.Idea.Arm.Fn.invertKey },
  Spec.Idea.ecbApi.artifact Arm.target {
    code := Impl.Idea.Arm.Fn.ecb
    verified := Proof.Idea.Arm.Fn.ecb }]

spec_apis artifacts

end VG.Artifacts.Idea.Arm
