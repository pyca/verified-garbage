module

public import VerifiedGarbage.Proof.Idea.Arm.Scrub
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # IDEA-OFB on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.IdeaOfb.Arm

def artifacts : List Artifact := [
  Spec.Idea.ofbApi.artifact Arm.target {
    code := Impl.Idea.Arm.Fn.ofb
    verified := .scrubbed Proof.Idea.Arm.Fn.ofb },
  Spec.Idea.ofbFinalApi.artifact Arm.target {
    code := Impl.Idea.Arm.Fn.ofbFinal
    verified := .scrubbed Proof.Idea.Arm.Fn.ofbFinal }]

end VG.Artifacts.IdeaOfb.Arm
