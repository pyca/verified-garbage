module

public import VerifiedGarbage.Proof.Idea.Arm.FbVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # IDEA-OFB artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.IdeaOfb.Arm

def artifacts : List Artifact := [
  Spec.Idea.ofbApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Idea.Arm.ofb
    stack := 96
    verified := Proof.Idea.Arm.ofb_framed }]

end VG.Artifacts.IdeaOfb.Arm
