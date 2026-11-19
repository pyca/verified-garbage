module

public import VerifiedGarbage.Proof.Sha3.Arm.Absorb
public import VerifiedGarbage.Proof.Sha3.Arm.Instances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # SHA-3 and SHAKE (FIPS 202) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sha3.Arm

def artifacts : List Artifact := [
  Spec.Sha3.absorbSha3_224Api.artifact Arm.target Proof.Sha3.Arm.Absorb.absorbSha3_224Reg,
  Spec.Sha3.finalizeSha3_224Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Instances.finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len
    verified := Proof.Sha3.Arm.Instances.finalize_sha3_224 },
  Spec.Sha3.absorbSha3_256Api.artifact Arm.target Proof.Sha3.Arm.Absorb.absorbSha3_256Reg,
  Spec.Sha3.finalizeSha3_256Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Instances.finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len
    verified := Proof.Sha3.Arm.Instances.finalize_sha3_256 },
  Spec.Sha3.absorbSha3_384Api.artifact Arm.target Proof.Sha3.Arm.Absorb.absorbSha3_384Reg,
  Spec.Sha3.finalizeSha3_384Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Instances.finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len
    verified := Proof.Sha3.Arm.Instances.finalize_sha3_384 },
  Spec.Sha3.absorbSha3_512Api.artifact Arm.target Proof.Sha3.Arm.Absorb.absorbSha3_512Reg,
  Spec.Sha3.finalizeSha3_512Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Instances.finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len
    verified := Proof.Sha3.Arm.Instances.finalize_sha3_512 },
  Spec.Sha3.absorbShake128Api.artifact Arm.target Proof.Sha3.Arm.Absorb.absorbShake128Reg,
  Spec.Sha3.finalizeShake128Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Instances.xofFinalize Spec.Sha3.xofShake128.rate
    verified := Proof.Sha3.Arm.Instances.finalize_shake128 },
  Spec.Sha3.squeezeShake128Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Instances.xofSqueeze Spec.Sha3.xofShake128.rate
    verified := Proof.Sha3.Arm.Instances.squeeze_shake128 },
  Spec.Sha3.finalizeShake256Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Instances.xofFinalize Spec.Sha3.xofShake256.rate
    verified := Proof.Sha3.Arm.Instances.finalize_shake256 },
  Spec.Sha3.squeezeShake256Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Instances.xofSqueeze Spec.Sha3.xofShake256.rate
    verified := Proof.Sha3.Arm.Instances.squeeze_shake256 }]

end VG.Artifacts.Sha3.Arm
