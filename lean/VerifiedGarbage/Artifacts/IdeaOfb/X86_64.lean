module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Ofb
public import VerifiedGarbage.Spec.Idea.OfbFinal
import VerifiedGarbage.Impl.Idea.X86_64.Fn
import VerifiedGarbage.Proof.Idea.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.X86_64.ModesLit
import VerifiedGarbage.Proof.Idea.X86_64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA-OFB on x86-64 -/

namespace VG.Artifacts.IdeaOfb.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Idea.ofbApi.artifact X86_64.target { code := Impl.Idea.X86_64.Fn.ofb, verified := Proof.Idea.X86_64.Scrub.ofb_scrubbed, spSafe := Proof.Idea.X86_64.Scrub.ofb_spSafe },
  Spec.Idea.ofbFinalApi.artifact X86_64.target { code := Impl.Idea.X86_64.Fn.ofbFinal, verified := Proof.Idea.X86_64.Scrub.ofbFinal_scrubbed, spSafe := Proof.Idea.X86_64.Scrub.ofbFinal_spSafe }]

spec_apis artifacts

end VG.Artifacts.IdeaOfb.X86_64
