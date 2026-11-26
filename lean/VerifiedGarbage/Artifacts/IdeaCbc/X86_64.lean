module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Cbc
import VerifiedGarbage.Impl.Idea.X86_64.Fn
import VerifiedGarbage.Proof.Idea.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.X86_64.ModesLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA-CBC on x86-64 -/

namespace VG.Artifacts.IdeaCbc.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Idea.cbcEncryptChainedApi.artifact X86_64.target { code := Impl.Idea.X86_64.Fn.cbcEncrypt, verified := Proof.Idea.X86_64.Scrub.cbcEncrypt_scrubbed, spSafe := Proof.Idea.X86_64.Scrub.cbcEncrypt_spSafe },
  Spec.Idea.cbcDecryptChainedApi.artifact X86_64.target { code := Impl.Idea.X86_64.Fn.cbcDecrypt, verified := Proof.Idea.X86_64.Scrub.cbcDecrypt_scrubbed, spSafe := Proof.Idea.X86_64.Scrub.cbcDecrypt_spSafe }]

spec_apis artifacts

end VG.Artifacts.IdeaCbc.X86_64
