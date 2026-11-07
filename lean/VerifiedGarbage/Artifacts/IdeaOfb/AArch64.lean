module

public import VerifiedGarbage.Proof.Idea.AArch64.FbVerified
public import VerifiedGarbage.Proof.Idea.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Idea.AArch64.ModesLit
import VerifiedGarbage.Proof.Idea.AArch64.FbFinalLit

/-! # IDEA-OFB artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.IdeaOfb.AArch64

def artifacts : List Artifact := [
  Spec.Idea.ofbApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.ofb
    stack := 208
    verified := Proof.Idea.AArch64.ofb_framed },
  Spec.Idea.ofbFinalApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.ofbFinal
    stack := 208
    verified := Proof.Idea.AArch64.ofbFinal_framed }]

end VG.Artifacts.IdeaOfb.AArch64
