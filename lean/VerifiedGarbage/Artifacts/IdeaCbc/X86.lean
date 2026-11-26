module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Cbc
import VerifiedGarbage.Proof.Idea.X86.Scrub
import VerifiedGarbage.Impl.Idea.X86.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.X86.ModesLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA-CBC on x86 -/

namespace VG.Artifacts.IdeaCbc.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Idea.cbcEncryptChainedApi.artifact X86.target {
    code := Impl.Idea.X86.Fn.cbcEncryptChained
    verified := Proof.Idea.X86.Scrub.cbcEncryptChained_scrubbed },
  Spec.Idea.cbcDecryptChainedApi.artifact X86.target {
    code := Impl.Idea.X86.Fn.cbcDecryptChained
    verified := Proof.Idea.X86.Scrub.cbcDecryptChained_scrubbed }]

spec_apis artifacts

end VG.Artifacts.IdeaCbc.X86
