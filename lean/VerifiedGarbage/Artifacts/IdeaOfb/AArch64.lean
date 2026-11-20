module

public import VerifiedGarbage.Impl.Idea.AArch64.Fn
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
    code := Impl.Idea.AArch64.Fn.ofb
    verified := .scrubbed Proof.Idea.AArch64.ModesResidue.ofbCode_scrubbed },
  Spec.Idea.ofbFinalApi.artifact AArch64.target {
    code := Impl.Idea.AArch64.Fn.ofbFinal
    verified := .scrubbed Proof.Idea.AArch64.ModesResidue.ofbFinalCode_scrubbed }]

end VG.Artifacts.IdeaOfb.AArch64
