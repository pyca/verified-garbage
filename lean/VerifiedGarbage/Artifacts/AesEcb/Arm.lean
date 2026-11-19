module

public import VerifiedGarbage.Proof.Aes.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES-ECB (NIST SP 800-38A §6.1) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesEcb.Arm

def artifacts : List Artifact := [
  Spec.AesEcb.encryptApi.artifact Arm.target Proof.Aes.Arm.Scrub.ecbEncryptReg,
  Spec.AesEcb.decryptApi.artifact Arm.target Proof.Aes.Arm.Scrub.ecbDecryptReg]

end VG.Artifacts.AesEcb.Arm
