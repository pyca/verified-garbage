module

public import VerifiedGarbage.Proof.Idea.AArch64.FbVerified
public import VerifiedGarbage.Proof.Idea.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Idea.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Idea.AArch64.ModesLit
import VerifiedGarbage.Proof.Idea.AArch64.FbFinalLit

/-! # IDEA-CFB64 on AArch64 -/

@[expose] public section

namespace VG.Artifacts.IdeaCfb.AArch64

def artifacts : List Artifact := [
  Spec.Idea.cfbEncryptApi.artifact AArch64.target {
    code := Proof.Idea.AArch64.ModesResidue.cfbEncryptCode
    verified := .scrubbed ⟨Proof.Idea.AArch64.ModesResidue.cfbEncryptCode_verified,
      Proof.Idea.AArch64.ModesResidue.cfbEncryptCode_noResidue⟩ },
  Spec.Idea.cfbDecryptApi.artifact AArch64.target {
    code := Proof.Idea.AArch64.ModesResidue.cfbDecryptCode
    verified := .scrubbed ⟨Proof.Idea.AArch64.ModesResidue.cfbDecryptCode_verified,
      Proof.Idea.AArch64.ModesResidue.cfbDecryptCode_noResidue⟩ },
  Spec.Idea.cfbEncryptFinalApi.artifact AArch64.target {
    code := Proof.Idea.AArch64.ModesResidue.cfbEncryptFinalCode
    verified := .scrubbed ⟨Proof.Idea.AArch64.ModesResidue.cfbEncryptFinalCode_verified,
      Proof.Idea.AArch64.ModesResidue.cfbEncryptFinalCode_noResidue⟩ },
  Spec.Idea.cfbDecryptFinalApi.artifact AArch64.target {
    code := Proof.Idea.AArch64.ModesResidue.cfbDecryptFinalCode
    verified := .scrubbed ⟨Proof.Idea.AArch64.ModesResidue.cfbDecryptFinalCode_verified,
      Proof.Idea.AArch64.ModesResidue.cfbDecryptFinalCode_noResidue⟩ }]

end VG.Artifacts.IdeaCfb.AArch64
