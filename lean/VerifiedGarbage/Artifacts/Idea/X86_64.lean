module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Contract
import VerifiedGarbage.Impl.Idea.X86_64.Fn
import VerifiedGarbage.Proof.Idea.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.X86_64.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA on x86-64 -/

namespace VG.Artifacts.Idea.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Idea.expandKeyApi.artifact X86_64.target { code := Impl.Idea.X86_64.Fn.expandKey, verified := Proof.Idea.X86_64.Scrub.expandKey_scrubbed, spSafe := Proof.Idea.X86_64.Scrub.expandKey_spSafe },
  Spec.Idea.invertKeyApi.artifact X86_64.target { code := Impl.Idea.X86_64.Fn.invertKey, verified := Proof.Idea.X86_64.Scrub.invertKey_scrubbed, spSafe := Proof.Idea.X86_64.Scrub.invertKey_spSafe },
  Spec.Idea.ecbApi.artifact X86_64.target { code := Impl.Idea.X86_64.Fn.ecb, verified := Proof.Idea.X86_64.Scrub.ecb_scrubbed, spSafe := Proof.Idea.X86_64.Scrub.ecb_spSafe }]

spec_apis artifacts

end VG.Artifacts.Idea.X86_64
