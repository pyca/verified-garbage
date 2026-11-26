module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Cfb
public import VerifiedGarbage.Spec.Idea.CfbFinal
import VerifiedGarbage.Impl.Idea.AArch64.Fn
import VerifiedGarbage.Proof.Idea.AArch64.FbVerified
import VerifiedGarbage.Proof.Idea.AArch64.FbFinalVerified
import VerifiedGarbage.Proof.Idea.AArch64.ModesResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.AArch64.ModesLit
import VerifiedGarbage.Proof.Idea.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA-CFB64 on AArch64 -/

namespace VG.Artifacts.IdeaCfb.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Idea.cfbEncryptApi.artifact AArch64.target {
    code := Impl.Idea.AArch64.Fn.cfbEncrypt
    verified := Proof.Idea.AArch64.ModesResidue.cfbEncryptCode_scrubbed },
  Spec.Idea.cfbDecryptApi.artifact AArch64.target {
    code := Impl.Idea.AArch64.Fn.cfbDecrypt
    verified := Proof.Idea.AArch64.ModesResidue.cfbDecryptCode_scrubbed },
  Spec.Idea.cfbEncryptFinalApi.artifact AArch64.target {
    code := Impl.Idea.AArch64.Fn.cfbEncryptFinal
    verified := Proof.Idea.AArch64.ModesResidue.cfbEncryptFinalCode_scrubbed },
  Spec.Idea.cfbDecryptFinalApi.artifact AArch64.target {
    code := Impl.Idea.AArch64.Fn.cfbDecryptFinal
    verified := Proof.Idea.AArch64.ModesResidue.cfbDecryptFinalCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.IdeaCfb.AArch64
