module

public import VerifiedGarbage.Proof.Aes.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesXts.Arm

def artifacts : List Artifact := [
  Spec.Xts.aesEncryptUnitApi.artifact Arm.target Proof.Aes.Arm.Scrub.xtsEncryptReg,
  Spec.Xts.aesDecryptUnitApi.artifact Arm.target Proof.Aes.Arm.Scrub.xtsDecryptReg]

end VG.Artifacts.AesXts.Arm
