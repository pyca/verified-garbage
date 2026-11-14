module

public import VerifiedGarbage.Proof.Idea.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Idea.X86_64.ModesLit
import VerifiedGarbage.Proof.Idea.X86_64.FbFinalLit

/-! # IDEA-CFB64 on x86-64 -/

@[expose] public section

namespace VG.Artifacts.IdeaCfb.X86_64

def artifacts : List Artifact := [
  Spec.Idea.cfbEncryptApi.artifact X86_64.target Proof.Idea.X86_64.Scrub.cfbEncryptReg,
  Spec.Idea.cfbDecryptApi.artifact X86_64.target Proof.Idea.X86_64.Scrub.cfbDecryptReg,
  Spec.Idea.cfbEncryptFinalApi.artifact X86_64.target Proof.Idea.X86_64.Scrub.cfbEncryptFinalReg,
  Spec.Idea.cfbDecryptFinalApi.artifact X86_64.target Proof.Idea.X86_64.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.IdeaCfb.X86_64
