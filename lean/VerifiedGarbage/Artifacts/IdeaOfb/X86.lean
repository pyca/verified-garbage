module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Ofb
public import VerifiedGarbage.Spec.Idea.OfbFinal
import VerifiedGarbage.Proof.Idea.X86.Scrub
import VerifiedGarbage.Impl.Idea.X86.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.X86.ModesLit
import VerifiedGarbage.Proof.Idea.X86.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA-OFB on x86 -/

namespace VG.Artifacts.IdeaOfb.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Idea.ofbApi.artifact X86.target {
    code := Impl.Idea.X86.Fn.ofb
    verified := Proof.Idea.X86.Scrub.ofb_scrubbed },
  Spec.Idea.ofbFinalApi.artifact X86.target {
    code := Impl.Idea.X86.Fn.ofbFinal
    verified := Proof.Idea.X86.Scrub.ofbFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.IdeaOfb.X86
