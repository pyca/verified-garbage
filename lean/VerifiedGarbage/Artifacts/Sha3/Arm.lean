module

public import VerifiedGarbage.Proof.Sha3.Arm.Absorb
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # SHA-3 and SHAKE (FIPS 202) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sha3.Arm

def artifacts : List Artifact := [
  Spec.Sha3.updateSha3_224Api.artifact Arm.target Proof.Sha3.Arm.Absorb.absorbSha3_224Reg,
  Spec.Sha3.finalizeSha3_224Api.artifact Arm.target Proof.Sha3.Arm.Absorb.finalizeSha3_224Reg,
  Spec.Sha3.updateSha3_256Api.artifact Arm.target Proof.Sha3.Arm.Absorb.absorbSha3_256Reg,
  Spec.Sha3.finalizeSha3_256Api.artifact Arm.target Proof.Sha3.Arm.Absorb.finalizeSha3_256Reg,
  Spec.Sha3.updateSha3_384Api.artifact Arm.target Proof.Sha3.Arm.Absorb.absorbSha3_384Reg,
  Spec.Sha3.finalizeSha3_384Api.artifact Arm.target Proof.Sha3.Arm.Absorb.finalizeSha3_384Reg,
  Spec.Sha3.updateSha3_512Api.artifact Arm.target Proof.Sha3.Arm.Absorb.absorbSha3_512Reg,
  Spec.Sha3.finalizeSha3_512Api.artifact Arm.target Proof.Sha3.Arm.Absorb.finalizeSha3_512Reg,
  Spec.Sha3.updateShake128Api.artifact Arm.target Proof.Sha3.Arm.Absorb.absorbShake128Reg,
  Spec.Sha3.finalizeShake128Api.artifact Arm.target Proof.Sha3.Arm.Absorb.finalizeShake128Reg,
  Spec.Sha3.squeezeShake128Api.artifact Arm.target Proof.Sha3.Arm.Absorb.squeezeShake128Reg,
  Spec.Sha3.finalizeShake256Api.artifact Arm.target Proof.Sha3.Arm.Absorb.finalizeShake256Reg,
  Spec.Sha3.squeezeShake256Api.artifact Arm.target Proof.Sha3.Arm.Absorb.squeezeShake256Reg]

end VG.Artifacts.Sha3.Arm
