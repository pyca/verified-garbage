module

public import VerifiedGarbage.Proof.Sha3.Arm.Absorb
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # SHA-3 and SHAKE (FIPS 202) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sha3.Arm

def artifacts : List Artifact := [
  Spec.Sha3.updateSha3_224Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Fn.update Spec.Sha3.hashSha3_224.rate
    verified := Proof.Sha3.Arm.Fn.update_sha3_224 },
  Spec.Sha3.finalizeSha3_224Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Fn.finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len
    verified := Proof.Sha3.Arm.Fn.finalize_sha3_224 },
  Spec.Sha3.updateSha3_256Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Fn.update Spec.Sha3.hashSha3_256.rate
    verified := Proof.Sha3.Arm.Fn.update_sha3_256 },
  Spec.Sha3.finalizeSha3_256Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Fn.finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len
    verified := Proof.Sha3.Arm.Fn.finalize_sha3_256 },
  Spec.Sha3.updateSha3_384Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Fn.update Spec.Sha3.hashSha3_384.rate
    verified := Proof.Sha3.Arm.Fn.update_sha3_384 },
  Spec.Sha3.finalizeSha3_384Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Fn.finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len
    verified := Proof.Sha3.Arm.Fn.finalize_sha3_384 },
  Spec.Sha3.updateSha3_512Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Fn.update Spec.Sha3.hashSha3_512.rate
    verified := Proof.Sha3.Arm.Fn.update_sha3_512 },
  Spec.Sha3.finalizeSha3_512Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Fn.finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len
    verified := Proof.Sha3.Arm.Fn.finalize_sha3_512 },
  Spec.Sha3.updateShake128Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Fn.update Spec.Sha3.xofShake128.rate
    verified := Proof.Sha3.Arm.Fn.update_shake128 },
  Spec.Sha3.finalizeShake128Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Fn.xofFinalize Spec.Sha3.xofShake128.rate
    verified := Proof.Sha3.Arm.Fn.finalize_shake128 },
  Spec.Sha3.squeezeShake128Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Fn.xofSqueeze Spec.Sha3.xofShake128.rate
    verified := Proof.Sha3.Arm.Fn.squeeze_shake128 },
  Spec.Sha3.finalizeShake256Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Fn.xofFinalize Spec.Sha3.xofShake256.rate
    verified := Proof.Sha3.Arm.Fn.finalize_shake256 },
  Spec.Sha3.squeezeShake256Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Fn.xofSqueeze Spec.Sha3.xofShake256.rate
    verified := Proof.Sha3.Arm.Fn.squeeze_shake256 }]

end VG.Artifacts.Sha3.Arm
