module

public import VerifiedGarbage.Proof.Idea.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Idea.X86.ModesLit
import VerifiedGarbage.Proof.Idea.X86.FbFinalLit

/-! # IDEA-CFB64 on x86 -/

@[expose] public section

namespace VG.Artifacts.IdeaCfb.X86

def artifacts : List Artifact := [
  Spec.Idea.cfbEncryptApi.artifact X86.target Proof.Idea.X86.Scrub.cfbEncryptReg,
  Spec.Idea.cfbDecryptApi.artifact X86.target Proof.Idea.X86.Scrub.cfbDecryptReg,
  Spec.Idea.cfbEncryptFinalApi.artifact X86.target Proof.Idea.X86.Scrub.cfbEncryptFinalReg,
  Spec.Idea.cfbDecryptFinalApi.artifact X86.target Proof.Idea.X86.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.IdeaCfb.X86
