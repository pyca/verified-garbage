module

public import VerifiedGarbage.Proof.Idea.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # IDEA-CBC artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.AArch64

def artifacts : List Artifact := [
  Spec.Idea.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cbcEncryptChained
    stack := 208
    verified := Proof.Idea.AArch64.cbcEncryptChained_framed },
  Spec.Idea.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cbcDecryptChained
    stack := 208
    verified := Proof.Idea.AArch64.cbcDecryptChained_framed }]

end VG.Artifacts.IdeaCbc.AArch64
