module

public import VerifiedGarbage.Proof.AesCcm.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES-CCM (NIST SP 800-38C) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesCcm.Arm

def artifacts : List Artifact := [
  Spec.Ccm.sealApi.artifact Arm.target Proof.AesCcm.Arm.Scrub.sealReg,
  Spec.Ccm.openApi.artifact Arm.target Proof.AesCcm.Arm.Scrub.openReg]

end VG.Artifacts.AesCcm.Arm
