module

public import VerifiedGarbage.Proof.Camellia.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Camellia-CFB128 on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.Arm

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact Arm.target Proof.Camellia.Arm.Scrub.cfbEncryptReg,
  Spec.Camellia.cfbDecryptApi.artifact Arm.target Proof.Camellia.Arm.Scrub.cfbDecryptReg,
  Spec.Camellia.cfbEncryptFinalApi.artifact Arm.target Proof.Camellia.Arm.Scrub.cfbEncryptFinalReg,
  Spec.Camellia.cfbDecryptFinalApi.artifact Arm.target Proof.Camellia.Arm.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.CamelliaCfb.Arm
