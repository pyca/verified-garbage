module

public import VerifiedGarbage.Proof.Idea.Arm.CbcVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # IDEA-CBC artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.Arm

def artifacts : List Artifact := [
  Spec.Idea.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Idea.Arm.cbcEncryptChained
    stack := 96
    verified := Proof.Idea.Arm.cbcEncryptChained_framed },
  Spec.Idea.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Idea.Arm.cbcDecryptChained
    stack := 96
    verified := Proof.Idea.Arm.cbcDecryptChained_framed }]

end VG.Artifacts.IdeaCbc.Arm
