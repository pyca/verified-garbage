module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Contract
import VerifiedGarbage.Proof.Idea.X86.Scrub
import VerifiedGarbage.Impl.Idea.X86.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.X86.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA on x86 -/

namespace VG.Artifacts.Idea.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Idea.expandKeyApi.artifact X86.target {
    code := Impl.Idea.X86.Fn.expandKey
    verified := Proof.Idea.X86.Scrub.expandKey_scrubbed },
  Spec.Idea.invertKeyApi.artifact X86.target {
    code := Impl.Idea.X86.Fn.invertKey
    verified := Proof.Idea.X86.Scrub.invertKey_scrubbed },
  Spec.Idea.ecbApi.artifact X86.target {
    code := Impl.Idea.X86.Fn.ecb
    verified := Proof.Idea.X86.Scrub.ecb_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Idea.X86
