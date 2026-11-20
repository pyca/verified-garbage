module

public import VerifiedGarbage.Proof.Idea.AArch64.FbVerified
public import VerifiedGarbage.Proof.Idea.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Idea.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Idea.AArch64.ModesLit
import VerifiedGarbage.Proof.Idea.AArch64.FbFinalLit

/-! # IDEA-OFB on AArch64 -/

@[expose] public section

namespace VG.Artifacts.IdeaOfb.AArch64

def artifacts : List Artifact := [
  Spec.Idea.ofbApi.artifact AArch64.target {
    code := Proof.Idea.AArch64.ModesResidue.ofbCode
    verified := .scrubbed ⟨Proof.Idea.AArch64.ModesResidue.ofbCode_verified,
      Proof.Idea.AArch64.ModesResidue.ofbCode_noResidue⟩ },
  Spec.Idea.ofbFinalApi.artifact AArch64.target {
    code := Proof.Idea.AArch64.ModesResidue.ofbFinalCode
    verified := .scrubbed ⟨Proof.Idea.AArch64.ModesResidue.ofbFinalCode_verified,
      Proof.Idea.AArch64.ModesResidue.ofbFinalCode_noResidue⟩ }]

end VG.Artifacts.IdeaOfb.AArch64
