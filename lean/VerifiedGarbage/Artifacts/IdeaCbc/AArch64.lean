module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Cbc
import VerifiedGarbage.Impl.Idea.AArch64.Fn
import VerifiedGarbage.Proof.Idea.AArch64.CbcVerified
import VerifiedGarbage.Proof.Idea.AArch64.ModesResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA-CBC on AArch64 -/

namespace VG.Artifacts.IdeaCbc.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Idea.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.Idea.AArch64.Fn.cbcEncryptChained
    verified := Proof.Idea.AArch64.ModesResidue.cbcEncryptChainedCode_scrubbed },
  Spec.Idea.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.Idea.AArch64.Fn.cbcDecryptChained
    verified := Proof.Idea.AArch64.ModesResidue.cbcDecryptChainedCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.IdeaCbc.AArch64
