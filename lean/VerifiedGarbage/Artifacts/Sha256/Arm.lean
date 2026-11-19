module

public import VerifiedGarbage.Proof.MdStream.Arm.ShaScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # SHA-256 (FIPS 180-4) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sha256.Arm

def artifacts : List Artifact := [
  Spec.Sha256.init224Api.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha224InitReg,
  Spec.Sha256.finalize224Api.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha224FinalizeReg,
  Spec.Sha256.digest224Api.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha224DigestReg,
  Spec.Sha256.initApi.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha256InitReg,
  Spec.Sha256.updateApi.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha256UpdateReg,
  Spec.Sha256.finalizeApi.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha256FinalizeReg,
  Spec.Sha256.digest256Api.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha256DigestReg]

end VG.Artifacts.Sha256.Arm
