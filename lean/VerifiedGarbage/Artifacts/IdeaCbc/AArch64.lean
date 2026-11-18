module

public import VerifiedGarbage.Proof.Idea.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Idea.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # IDEA-CBC on AArch64 -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.AArch64

def artifacts : List Artifact := [
  Spec.Idea.cbcEncryptChainedApi.artifact AArch64.target {
    code := Proof.Idea.AArch64.ModesResidue.cbcEncryptChainedCode
    verified := Proof.Idea.AArch64.ModesResidue.cbcEncryptChainedCode_verified
    residue := some ⟨Proof.Idea.AArch64.ModesResidue.cbcEncryptChainedCode_noResidue⟩ },
  Spec.Idea.cbcDecryptChainedApi.artifact AArch64.target {
    code := Proof.Idea.AArch64.ModesResidue.cbcDecryptChainedCode
    verified := Proof.Idea.AArch64.ModesResidue.cbcDecryptChainedCode_verified
    residue := some ⟨Proof.Idea.AArch64.ModesResidue.cbcDecryptChainedCode_noResidue⟩ }]

end VG.Artifacts.IdeaCbc.AArch64
