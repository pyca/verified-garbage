module

public import VerifiedGarbage.Proof.Gcm.Arm.Law
public import VerifiedGarbage.Proof.AesGcm.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES-GCM (NIST SP 800-38D) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesGcm.Arm

def artifacts : List Artifact := [
  Spec.Gcm.initApi.artifact Arm.target Proof.AesGcm.Arm.Scrub.initReg,
  Spec.Gcm.sealApi.artifact Arm.target Proof.AesGcm.Arm.Scrub.sealReg,
  Spec.Gcm.openApi.artifact Arm.target Proof.AesGcm.Arm.Scrub.openReg,
  Spec.Gcm.streamInitApi.artifact Arm.target Proof.AesGcm.Arm.Scrub.streamInitReg,
  Spec.Gcm.streamAadApi.artifact Arm.target Proof.AesGcm.Arm.Scrub.streamAadReg,
  Spec.Gcm.streamEncryptApi.artifact Arm.target Proof.AesGcm.Arm.Scrub.streamEncryptReg,
  Spec.Gcm.streamDecryptApi.artifact Arm.target Proof.AesGcm.Arm.Scrub.streamDecryptReg,
  Spec.Gcm.streamFinishApi.artifact Arm.target Proof.AesGcm.Arm.Scrub.streamFinishReg,
  Spec.Gcm.streamVerifyApi.artifact Arm.target Proof.AesGcm.Arm.Scrub.streamVerifyReg,
  Spec.Gcm.sealGatherApi.artifact Arm.target Proof.AesGcm.Arm.Scrub.sealGatherReg,
  Spec.Gcm.openToApi.artifact Arm.target Proof.AesGcm.Arm.Scrub.openToReg]

end VG.Artifacts.AesGcm.Arm
