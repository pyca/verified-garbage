module

public import VerifiedGarbage.Proof.Idea.X86.Scrub
public import VerifiedGarbage.Impl.Idea.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Idea.X86.ModesLit

/-! # IDEA-CBC on x86 -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.X86

def artifacts : List Artifact := [
  Spec.Idea.cbcEncryptChainedApi.artifact X86.target {
    code := Impl.Idea.X86.Fn.cbcEncryptChained
    verified := Proof.Idea.X86.Scrub.cbcEncryptChained_scrubbed },
  Spec.Idea.cbcDecryptChainedApi.artifact X86.target {
    code := Impl.Idea.X86.Fn.cbcDecryptChained
    verified := Proof.Idea.X86.Scrub.cbcDecryptChained_scrubbed }]

end VG.Artifacts.IdeaCbc.X86
