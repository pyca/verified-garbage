module

public import VerifiedGarbage.Proof.Idea.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Idea.X86_64.Lit

/-! # IDEA on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Idea.X86_64

def artifacts : List Artifact := [
  Spec.Idea.expandKeyApi.artifact X86_64.target Proof.Idea.X86_64.Scrub.expandKeyReg,
  Spec.Idea.invertKeyApi.artifact X86_64.target Proof.Idea.X86_64.Scrub.invertKeyReg,
  Spec.Idea.ecbApi.artifact X86_64.target Proof.Idea.X86_64.Scrub.ecbReg]

end VG.Artifacts.Idea.X86_64
