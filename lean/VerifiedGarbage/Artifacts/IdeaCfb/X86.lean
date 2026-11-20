module

public import VerifiedGarbage.Proof.Idea.X86.Scrub
public import VerifiedGarbage.Impl.Idea.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Idea.X86.ModesLit
import VerifiedGarbage.Proof.Idea.X86.FbFinalLit

/-! # IDEA-CFB64 on x86 -/

@[expose] public section

namespace VG.Artifacts.IdeaCfb.X86

def artifacts : List Artifact := [
  Spec.Idea.cfbEncryptApi.artifact X86.target {
    code := Impl.Idea.X86.Fn.cfbEncrypt
    verified := .scrubbed Proof.Idea.X86.Scrub.cfbEncrypt_scrubbed },
  Spec.Idea.cfbDecryptApi.artifact X86.target {
    code := Impl.Idea.X86.Fn.cfbDecrypt
    verified := .scrubbed Proof.Idea.X86.Scrub.cfbDecrypt_scrubbed },
  Spec.Idea.cfbEncryptFinalApi.artifact X86.target {
    code := Impl.Idea.X86.Fn.cfbEncryptFinal
    verified := .scrubbed Proof.Idea.X86.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Idea.cfbDecryptFinalApi.artifact X86.target {
    code := Impl.Idea.X86.Fn.cfbDecryptFinal
    verified := .scrubbed Proof.Idea.X86.Scrub.cfbDecryptFinal_scrubbed }]

end VG.Artifacts.IdeaCfb.X86
