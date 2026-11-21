module

public import VerifiedGarbage.Impl.Idea.AArch64.Fn
public import VerifiedGarbage.Proof.Idea.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Idea.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # IDEA-CBC on AArch64 -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.AArch64

def artifacts : List Artifact := [
  Spec.Idea.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.Idea.AArch64.Fn.cbcEncryptChained
    verified := Proof.Idea.AArch64.ModesResidue.cbcEncryptChainedCode_scrubbed },
  Spec.Idea.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.Idea.AArch64.Fn.cbcDecryptChained
    verified := Proof.Idea.AArch64.ModesResidue.cbcDecryptChainedCode_scrubbed }]

end VG.Artifacts.IdeaCbc.AArch64
