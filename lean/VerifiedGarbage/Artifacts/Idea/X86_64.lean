module

public import VerifiedGarbage.Impl.Idea.X86_64.Fn
public import VerifiedGarbage.Proof.Idea.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Idea.X86_64.Lit

/-! # IDEA on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Idea.X86_64

def artifacts : List Artifact := [
  Spec.Idea.expandKeyApi.artifact X86_64.target { code := Impl.Idea.X86_64.Fn.expandKey, verified := .scrubbed Proof.Idea.X86_64.Scrub.expandKey_scrubbed, spSafe := Proof.Idea.X86_64.Scrub.expandKey_spSafe },
  Spec.Idea.invertKeyApi.artifact X86_64.target { code := Impl.Idea.X86_64.Fn.invertKey, verified := .scrubbed Proof.Idea.X86_64.Scrub.invertKey_scrubbed, spSafe := Proof.Idea.X86_64.Scrub.invertKey_spSafe },
  Spec.Idea.ecbApi.artifact X86_64.target { code := Impl.Idea.X86_64.Fn.ecb, verified := .scrubbed Proof.Idea.X86_64.Scrub.ecb_scrubbed, spSafe := Proof.Idea.X86_64.Scrub.ecb_spSafe }]

end VG.Artifacts.Idea.X86_64
