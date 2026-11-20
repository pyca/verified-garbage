module

public import VerifiedGarbage.Impl.Idea.X86_64.Fn
public import VerifiedGarbage.Proof.Idea.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Idea.X86_64.ModesLit

/-! # IDEA-CBC on x86-64 -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.X86_64

def artifacts : List Artifact := [
  Spec.Idea.cbcEncryptChainedApi.artifact X86_64.target { code := Impl.Idea.X86_64.Fn.cbcEncrypt, verified := .scrubbed Proof.Idea.X86_64.Scrub.cbcEncrypt_scrubbed, spSafe := Proof.Idea.X86_64.Scrub.cbcEncrypt_spSafe },
  Spec.Idea.cbcDecryptChainedApi.artifact X86_64.target { code := Impl.Idea.X86_64.Fn.cbcDecrypt, verified := .scrubbed Proof.Idea.X86_64.Scrub.cbcDecrypt_scrubbed, spSafe := Proof.Idea.X86_64.Scrub.cbcDecrypt_spSafe }]

end VG.Artifacts.IdeaCbc.X86_64
