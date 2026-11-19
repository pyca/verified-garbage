module

public import VerifiedGarbage.Proof.Md5.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # MD5 (RFC 1321) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Md5.Arm

def artifacts : List Artifact := [
  Spec.Md5.initApi.artifact Arm.target Proof.Md5.Arm.Scrub.initReg,
  Spec.Md5.updateApi.artifact Arm.target Proof.Md5.Arm.Scrub.updateReg,
  Spec.Md5.finalizeApi.artifact Arm.target Proof.Md5.Arm.Scrub.finalizeReg]

end VG.Artifacts.Md5.Arm
