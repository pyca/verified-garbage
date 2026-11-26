module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Cbc
import VerifiedGarbage.Proof.Idea.Arm.Scrub
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA-CBC on ARMv7 -/

namespace VG.Artifacts.IdeaCbc.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Idea.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.Idea.Arm.Fn.cbcEncryptChained
    verified := Proof.Idea.Arm.Fn.cbcEncryptChained },
  Spec.Idea.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.Idea.Arm.Fn.cbcDecryptChained
    verified := Proof.Idea.Arm.Fn.cbcDecryptChained }]

spec_apis artifacts

end VG.Artifacts.IdeaCbc.Arm
