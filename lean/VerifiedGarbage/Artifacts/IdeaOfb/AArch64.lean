module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Ofb
public import VerifiedGarbage.Spec.Idea.OfbFinal
import VerifiedGarbage.Impl.Idea.AArch64.Fn
import VerifiedGarbage.Proof.Idea.AArch64.FbVerified
import VerifiedGarbage.Proof.Idea.AArch64.FbFinalVerified
import VerifiedGarbage.Proof.Idea.AArch64.ModesResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.AArch64.ModesLit
import VerifiedGarbage.Proof.Idea.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA-OFB on AArch64 -/

namespace VG.Artifacts.IdeaOfb.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Idea.ofbApi.artifact AArch64.target {
    code := Impl.Idea.AArch64.Fn.ofb
    verified := Proof.Idea.AArch64.ModesResidue.ofbCode_scrubbed },
  Spec.Idea.ofbFinalApi.artifact AArch64.target {
    code := Impl.Idea.AArch64.Fn.ofbFinal
    verified := Proof.Idea.AArch64.ModesResidue.ofbFinalCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.IdeaOfb.AArch64
