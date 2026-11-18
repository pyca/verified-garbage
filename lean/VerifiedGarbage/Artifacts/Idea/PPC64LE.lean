module

public import VerifiedGarbage.Proof.Idea.PPC64LE.Invert
public import VerifiedGarbage.Proof.Idea.PPC64LE.Key
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Idea.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Idea.PPC64LE.Lit

/-! # IDEA on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Idea.PPC64LE

def artifacts : List Artifact := [
  Spec.Idea.expandKeyApi.artifact PPC64LE.target Proof.Idea.PPC64LE.Scrub.expandKeyReg,
  Spec.Idea.invertKeyApi.artifact PPC64LE.target Proof.Idea.PPC64LE.Scrub.invertKeyReg,
  Spec.Idea.ecbApi.artifact PPC64LE.target Proof.Idea.PPC64LE.Scrub.ecbReg]

end VG.Artifacts.Idea.PPC64LE
