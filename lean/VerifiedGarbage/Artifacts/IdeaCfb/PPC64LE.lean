module

public import VerifiedGarbage.Proof.Idea.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Idea.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Idea.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Idea.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Idea.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Idea.PPC64LE.FbFinalLit

/-! # IDEA-CFB64 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.IdeaCfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Idea.cfbEncryptApi.artifact PPC64LE.target Proof.Idea.PPC64LE.Scrub.cfbEncryptReg,
  Spec.Idea.cfbDecryptApi.artifact PPC64LE.target Proof.Idea.PPC64LE.Scrub.cfbDecryptReg,
  Spec.Idea.cfbEncryptFinalApi.artifact PPC64LE.target Proof.Idea.PPC64LE.Scrub.cfbEncryptFinalReg,
  Spec.Idea.cfbDecryptFinalApi.artifact PPC64LE.target Proof.Idea.PPC64LE.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.IdeaCfb.PPC64LE
