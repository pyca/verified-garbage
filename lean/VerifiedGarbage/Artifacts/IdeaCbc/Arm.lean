module

public import VerifiedGarbage.Proof.Idea.Arm.Scrub
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # IDEA-CBC on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.Arm

def artifacts : List Artifact := [
  Spec.Idea.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.Idea.Arm.Fn.cbcEncryptChained
    verified := Proof.Idea.Arm.Fn.cbcEncryptChained },
  Spec.Idea.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.Idea.Arm.Fn.cbcDecryptChained
    verified := Proof.Idea.Arm.Fn.cbcDecryptChained }]

end VG.Artifacts.IdeaCbc.Arm
