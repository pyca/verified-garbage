module

public import VerifiedGarbage.Proof.Idea.AArch64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # IDEA-OFB artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.IdeaOfb.AArch64

def artifacts : List Artifact := [
  Spec.Idea.ofbApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.ofb
    stack := 208
    verified := Proof.Idea.AArch64.ofb_framed }]

end VG.Artifacts.IdeaOfb.AArch64
