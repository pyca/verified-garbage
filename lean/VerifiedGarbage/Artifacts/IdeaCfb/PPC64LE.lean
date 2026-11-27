module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Cfb
public import VerifiedGarbage.Spec.Idea.CfbFinal
import VerifiedGarbage.Proof.Idea.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.Idea.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.Idea.PPC64LE.FbFinalVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.PPC64LE.Scrub
import VerifiedGarbage.Proof.Idea.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Idea.PPC64LE.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA-CFB64 on PPC64LE -/

namespace VG.Artifacts.IdeaCfb.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Idea.cfbEncryptApi.artifact PPC64LE.target {
    code := Impl.Idea.PPC64LE.Fn.cfbEncrypt
    verified := Proof.Idea.PPC64LE.Scrub.cfbEncrypt_scrubbed },
  Spec.Idea.cfbDecryptApi.artifact PPC64LE.target {
    code := Impl.Idea.PPC64LE.Fn.cfbDecrypt
    verified := Proof.Idea.PPC64LE.Scrub.cfbDecrypt_scrubbed },
  Spec.Idea.cfbEncryptFinalApi.artifact PPC64LE.target {
    code := Impl.Idea.PPC64LE.Fn.cfbEncryptFinal
    verified := Proof.Idea.PPC64LE.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Idea.cfbDecryptFinalApi.artifact PPC64LE.target {
    code := Impl.Idea.PPC64LE.Fn.cfbDecryptFinal
    verified := Proof.Idea.PPC64LE.Scrub.cfbDecryptFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.IdeaCfb.PPC64LE
