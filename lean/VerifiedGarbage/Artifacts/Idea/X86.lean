module

public import VerifiedGarbage.Proof.Idea.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Idea.X86.Lit

/-! # IDEA on x86 -/

@[expose] public section

namespace VG.Artifacts.Idea.X86

def artifacts : List Artifact := [
  Spec.Idea.expandKeyApi.artifact X86.target Proof.Idea.X86.Scrub.expandKeyReg,
  Spec.Idea.invertKeyApi.artifact X86.target Proof.Idea.X86.Scrub.invertKeyReg,
  Spec.Idea.ecbApi.artifact X86.target Proof.Idea.X86.Scrub.ecbReg]

end VG.Artifacts.Idea.X86
