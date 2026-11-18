module

public import VerifiedGarbage.Proof.Idea.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Idea.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Idea.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Idea.PPC64LE.ModesLit

/-! # IDEA-CBC on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.PPC64LE

def artifacts : List Artifact := [
  Spec.Idea.cbcEncryptChainedApi.artifact PPC64LE.target Proof.Idea.PPC64LE.Scrub.cbcEncryptChainedReg,
  Spec.Idea.cbcDecryptChainedApi.artifact PPC64LE.target Proof.Idea.PPC64LE.Scrub.cbcDecryptChainedReg]

end VG.Artifacts.IdeaCbc.PPC64LE
