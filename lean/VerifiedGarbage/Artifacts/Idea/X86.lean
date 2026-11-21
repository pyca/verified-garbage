module

public import VerifiedGarbage.Proof.Idea.X86.Scrub
public import VerifiedGarbage.Impl.Idea.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Idea.X86.Lit

/-! # IDEA on x86 -/

@[expose] public section

namespace VG.Artifacts.Idea.X86

def artifacts : List Artifact := [
  Spec.Idea.expandKeyApi.artifact X86.target {
    code := Impl.Idea.X86.Fn.expandKey
    verified := Proof.Idea.X86.Scrub.expandKey_scrubbed },
  Spec.Idea.invertKeyApi.artifact X86.target {
    code := Impl.Idea.X86.Fn.invertKey
    verified := Proof.Idea.X86.Scrub.invertKey_scrubbed },
  Spec.Idea.ecbApi.artifact X86.target {
    code := Impl.Idea.X86.Fn.ecb
    verified := Proof.Idea.X86.Scrub.ecb_scrubbed }]

end VG.Artifacts.Idea.X86
