module

public import VerifiedGarbage.Proof.Aes.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES-CBC (NIST SP 800-38A §6.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesCbc.Arm

def artifacts : List Artifact := [
  Spec.Cbc.aesEncryptApi.artifact Arm.target Proof.Aes.Arm.Scrub.cbcEncryptReg,
  Spec.Cbc.aesDecryptApi.artifact Arm.target Proof.Aes.Arm.Scrub.cbcDecryptReg]

end VG.Artifacts.AesCbc.Arm
