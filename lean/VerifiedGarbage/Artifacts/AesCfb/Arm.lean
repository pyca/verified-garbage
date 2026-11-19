module

public import VerifiedGarbage.Proof.Aes.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesCfb.Arm

def artifacts : List Artifact := [
  Spec.Cfb.aesEncryptApi.artifact Arm.target Proof.Aes.Arm.Scrub.cfbEncryptReg,
  Spec.Cfb.aesDecryptApi.artifact Arm.target Proof.Aes.Arm.Scrub.cfbDecryptReg,
  Spec.Cfb.aesEncryptFinalApi.artifact Arm.target Proof.Aes.Arm.Scrub.cfbEncryptFinalReg,
  Spec.Cfb.aesDecryptFinalApi.artifact Arm.target Proof.Aes.Arm.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.AesCfb.Arm
