module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FbFinalLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit

/-! # Triple DES-OFB on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.TripleDesOfb.PPC64LE

def artifacts : List Artifact := [
  Spec.TripleDes.ofbApi.artifact PPC64LE.target Proof.TripleDes.PPC64LE.Scrub.ofbReg,
  Spec.TripleDes.ofbFinalApi.artifact PPC64LE.target Proof.TripleDes.PPC64LE.Scrub.ofbFinalReg]

end VG.Artifacts.TripleDesOfb.PPC64LE
