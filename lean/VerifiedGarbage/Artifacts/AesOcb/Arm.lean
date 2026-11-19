module

public import VerifiedGarbage.Proof.AesOcb.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES-OCB (RFC 7253) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesOcb.Arm

def artifacts : List Artifact := [
  Spec.Ocb.initApi.artifact Arm.target Proof.AesOcb.Arm.Scrub.initReg,
  Spec.Ocb.sealApi.artifact Arm.target Proof.AesOcb.Arm.Scrub.sealReg,
  Spec.Ocb.openApi.artifact Arm.target Proof.AesOcb.Arm.Scrub.openReg]

end VG.Artifacts.AesOcb.Arm
