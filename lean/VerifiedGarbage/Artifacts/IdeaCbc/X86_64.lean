module

public import VerifiedGarbage.Proof.Idea.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Idea.X86_64.ModesLit

/-! # IDEA-CBC on x86-64 -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.X86_64

def artifacts : List Artifact := [
  Spec.Idea.cbcEncryptChainedApi.artifact X86_64.target Proof.Idea.X86_64.Scrub.cbcEncryptReg,
  Spec.Idea.cbcDecryptChainedApi.artifact X86_64.target Proof.Idea.X86_64.Scrub.cbcDecryptReg]

end VG.Artifacts.IdeaCbc.X86_64
