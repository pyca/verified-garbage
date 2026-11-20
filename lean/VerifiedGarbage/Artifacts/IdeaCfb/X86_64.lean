module

public import VerifiedGarbage.Impl.Idea.X86_64.Fn
public import VerifiedGarbage.Proof.Idea.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Idea.X86_64.ModesLit
import VerifiedGarbage.Proof.Idea.X86_64.FbFinalLit

/-! # IDEA-CFB64 on x86-64 -/

@[expose] public section

namespace VG.Artifacts.IdeaCfb.X86_64

def artifacts : List Artifact := [
  Spec.Idea.cfbEncryptApi.artifact X86_64.target { code := Impl.Idea.X86_64.Fn.cfbEncrypt, verified := .scrubbed Proof.Idea.X86_64.Scrub.cfbEncrypt_scrubbed, spSafe := Proof.Idea.X86_64.Scrub.cfbEncrypt_spSafe },
  Spec.Idea.cfbDecryptApi.artifact X86_64.target { code := Impl.Idea.X86_64.Fn.cfbDecrypt, verified := .scrubbed Proof.Idea.X86_64.Scrub.cfbDecrypt_scrubbed, spSafe := Proof.Idea.X86_64.Scrub.cfbDecrypt_spSafe },
  Spec.Idea.cfbEncryptFinalApi.artifact X86_64.target { code := Impl.Idea.X86_64.Fn.cfbEncryptFinal, verified := .scrubbed Proof.Idea.X86_64.Scrub.cfbEncryptFinal_scrubbed, spSafe := Proof.Idea.X86_64.Scrub.cfbEncryptFinal_spSafe },
  Spec.Idea.cfbDecryptFinalApi.artifact X86_64.target { code := Impl.Idea.X86_64.Fn.cfbDecryptFinal, verified := .scrubbed Proof.Idea.X86_64.Scrub.cfbDecryptFinal_scrubbed, spSafe := Proof.Idea.X86_64.Scrub.cfbDecryptFinal_spSafe }]

end VG.Artifacts.IdeaCfb.X86_64
