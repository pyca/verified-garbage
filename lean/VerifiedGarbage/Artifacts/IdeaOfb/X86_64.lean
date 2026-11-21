module

public import VerifiedGarbage.Impl.Idea.X86_64.Fn
public import VerifiedGarbage.Proof.Idea.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Idea.X86_64.ModesLit
import VerifiedGarbage.Proof.Idea.X86_64.FbFinalLit

/-! # IDEA-OFB on x86-64 -/

@[expose] public section

namespace VG.Artifacts.IdeaOfb.X86_64

def artifacts : List Artifact := [
  Spec.Idea.ofbApi.artifact X86_64.target { code := Impl.Idea.X86_64.Fn.ofb, verified := Proof.Idea.X86_64.Scrub.ofb_scrubbed, spSafe := Proof.Idea.X86_64.Scrub.ofb_spSafe },
  Spec.Idea.ofbFinalApi.artifact X86_64.target { code := Impl.Idea.X86_64.Fn.ofbFinal, verified := Proof.Idea.X86_64.Scrub.ofbFinal_scrubbed, spSafe := Proof.Idea.X86_64.Scrub.ofbFinal_spSafe }]

end VG.Artifacts.IdeaOfb.X86_64
