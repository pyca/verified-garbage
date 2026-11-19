module

public import VerifiedGarbage.Proof.MdStream.Arm.ShaScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # SHA-1 (FIPS 180-4) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sha1.Arm

def artifacts : List Artifact := [
  Spec.Sha1.initApi.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha1InitReg,
  Spec.Sha1.updateApi.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha1UpdateReg,
  Spec.Sha1.finalizeApi.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha1FinalizeReg,
  Spec.Sha1.digestApi.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha1DigestReg]

end VG.Artifacts.Sha1.Arm
