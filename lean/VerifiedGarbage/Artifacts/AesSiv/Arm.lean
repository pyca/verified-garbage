module

public import VerifiedGarbage.Proof.AesSiv.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES-SIV (RFC 5297) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesSiv.Arm

def artifacts : List Artifact := [
  Spec.Siv.initApi.artifact Arm.target Proof.AesSiv.Arm.Scrub.initReg,
  Spec.Siv.encryptApi.artifact Arm.target Proof.AesSiv.Arm.Scrub.encryptReg,
  Spec.Siv.decryptApi.artifact Arm.target Proof.AesSiv.Arm.Scrub.decryptReg]

end VG.Artifacts.AesSiv.Arm
