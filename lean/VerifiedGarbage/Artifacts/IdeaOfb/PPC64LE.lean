module

public import VerifiedGarbage.Proof.Idea.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Idea.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Idea.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Idea.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Idea.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Idea.PPC64LE.FbFinalLit

/-! # IDEA-OFB on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.IdeaOfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Idea.ofbApi.artifact PPC64LE.target Proof.Idea.PPC64LE.Scrub.ofbReg,
  Spec.Idea.ofbFinalApi.artifact PPC64LE.target Proof.Idea.PPC64LE.Scrub.ofbFinalReg]

end VG.Artifacts.IdeaOfb.PPC64LE
