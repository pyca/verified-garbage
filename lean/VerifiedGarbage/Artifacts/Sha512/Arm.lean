module

public import VerifiedGarbage.Proof.MdStream.Arm.ShaScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sha512.Arm

def artifacts : List Artifact := [
  Spec.Sha512.init384Api.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha384InitReg,
  Spec.Sha512.init512Api.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha512InitReg,
  Spec.Sha512.init512_224Api.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha512_224InitReg,
  Spec.Sha512.init512_256Api.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha512_256InitReg,
  Spec.Sha512.updateApi.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha512UpdateReg,
  Spec.Sha512.finalizeApi.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha512FinalizeReg,
  Spec.Sha512.finalize384Api.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha384FinalizeReg,
  Spec.Sha512.finalize512_256Api.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha512_256FinalizeReg,
  Spec.Sha512.finalize512_224Api.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha512_224FinalizeReg,
  Spec.Sha512.digest384Api.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha384DigestReg,
  Spec.Sha512.digest512Api.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha512DigestReg,
  Spec.Sha512.digest512_224Api.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha512_224DigestReg,
  Spec.Sha512.digest512_256Api.artifact Arm.target Proof.MdStream.Arm.ShaScrub.sha512_256DigestReg]

end VG.Artifacts.Sha512.Arm
