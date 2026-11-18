module

public import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Cast5.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Cast5.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Cast5.PPC64LE.FbFinalLit

/-! # CAST5-OFB on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Cast5Ofb.PPC64LE

def artifacts : List Artifact := [
  Spec.Cast5.ofbApi.artifact PPC64LE.target Proof.Cast5.PPC64LE.Scrub.ofbReg,
  Spec.Cast5.ofbFinalApi.artifact PPC64LE.target Proof.Cast5.PPC64LE.Scrub.ofbFinalReg]

end VG.Artifacts.Cast5Ofb.PPC64LE
