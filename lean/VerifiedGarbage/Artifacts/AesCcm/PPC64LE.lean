module

public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # AES-CCM (NIST SP 800-38C) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesCcm.PPC64LE

def artifacts : List Artifact := [
  Spec.Ccm.sealApi.artifact PPC64LE.target Proof.AesCcm.PPC64LE.Scrub.sealReg,
  Spec.Ccm.openApi.artifact PPC64LE.target Proof.AesCcm.PPC64LE.Scrub.openReg]

end VG.Artifacts.AesCcm.PPC64LE
