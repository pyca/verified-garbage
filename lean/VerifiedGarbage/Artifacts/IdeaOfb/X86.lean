module

public import VerifiedGarbage.Proof.Idea.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Idea.X86.ModesLit
import VerifiedGarbage.Proof.Idea.X86.FbFinalLit

/-! # IDEA-OFB on x86 -/

@[expose] public section

namespace VG.Artifacts.IdeaOfb.X86

def artifacts : List Artifact := [
  Spec.Idea.ofbApi.artifact X86.target Proof.Idea.X86.Scrub.ofbReg,
  Spec.Idea.ofbFinalApi.artifact X86.target Proof.Idea.X86.Scrub.ofbFinalReg]

end VG.Artifacts.IdeaOfb.X86
