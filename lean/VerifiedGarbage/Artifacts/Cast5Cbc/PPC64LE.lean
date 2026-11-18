module

public import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Cast5.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesLit

/-! # CAST5-CBC on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Cast5Cbc.PPC64LE

def artifacts : List Artifact := [
  Spec.Cast5.cbcEncryptChainedApi.artifact PPC64LE.target Proof.Cast5.PPC64LE.Scrub.cbcEncryptChainedReg,
  Spec.Cast5.cbcDecryptChainedApi.artifact PPC64LE.target Proof.Cast5.PPC64LE.Scrub.cbcDecryptChainedReg]

end VG.Artifacts.Cast5Cbc.PPC64LE
