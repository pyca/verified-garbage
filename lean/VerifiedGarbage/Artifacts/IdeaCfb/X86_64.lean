module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Cfb
public import VerifiedGarbage.Spec.Idea.CfbFinal
import VerifiedGarbage.Impl.Idea.X86_64.Fn
import VerifiedGarbage.Proof.Idea.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.X86_64.ModesLit
import VerifiedGarbage.Proof.Idea.X86_64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA-CFB64 on x86-64 -/

namespace VG.Artifacts.IdeaCfb.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Idea.cfbEncryptApi.artifact X86_64.target { code := Impl.Idea.X86_64.Fn.cfbEncrypt, verified := Proof.Idea.X86_64.Scrub.cfbEncrypt_scrubbed, spSafe := Proof.Idea.X86_64.Scrub.cfbEncrypt_spSafe },
  Spec.Idea.cfbDecryptApi.artifact X86_64.target { code := Impl.Idea.X86_64.Fn.cfbDecrypt, verified := Proof.Idea.X86_64.Scrub.cfbDecrypt_scrubbed, spSafe := Proof.Idea.X86_64.Scrub.cfbDecrypt_spSafe },
  Spec.Idea.cfbEncryptFinalApi.artifact X86_64.target { code := Impl.Idea.X86_64.Fn.cfbEncryptFinal, verified := Proof.Idea.X86_64.Scrub.cfbEncryptFinal_scrubbed, spSafe := Proof.Idea.X86_64.Scrub.cfbEncryptFinal_spSafe },
  Spec.Idea.cfbDecryptFinalApi.artifact X86_64.target { code := Impl.Idea.X86_64.Fn.cfbDecryptFinal, verified := Proof.Idea.X86_64.Scrub.cfbDecryptFinal_scrubbed, spSafe := Proof.Idea.X86_64.Scrub.cfbDecryptFinal_spSafe }]

spec_apis artifacts

end VG.Artifacts.IdeaCfb.X86_64
