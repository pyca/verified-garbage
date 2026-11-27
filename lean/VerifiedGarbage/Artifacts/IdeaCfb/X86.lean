module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Cfb
public import VerifiedGarbage.Spec.Idea.CfbFinal
import VerifiedGarbage.Proof.Idea.X86.Scrub
import VerifiedGarbage.Impl.Idea.X86.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.X86.ModesLit
import VerifiedGarbage.Proof.Idea.X86.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA-CFB64 on x86 -/

namespace VG.Artifacts.IdeaCfb.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Idea.cfbEncryptApi.artifact X86.target {
    code := Impl.Idea.X86.Fn.cfbEncrypt
    verified := Proof.Idea.X86.Scrub.cfbEncrypt_scrubbed },
  Spec.Idea.cfbDecryptApi.artifact X86.target {
    code := Impl.Idea.X86.Fn.cfbDecrypt
    verified := Proof.Idea.X86.Scrub.cfbDecrypt_scrubbed },
  Spec.Idea.cfbEncryptFinalApi.artifact X86.target {
    code := Impl.Idea.X86.Fn.cfbEncryptFinal
    verified := Proof.Idea.X86.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Idea.cfbDecryptFinalApi.artifact X86.target {
    code := Impl.Idea.X86.Fn.cfbDecryptFinal
    verified := Proof.Idea.X86.Scrub.cfbDecryptFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.IdeaCfb.X86
