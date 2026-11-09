module

public import VerifiedGarbage.Proof.Sha3.Arm.Instances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # SHA-3 and SHAKE (FIPS 202) on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.Sha3.Arm

def artifacts : List Artifact := [
  Spec.Sha3.updateSha3_224Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Instances.update Spec.Sha3.hashSha3_224.rate
    stack := 16
    verified := Proof.Sha3.Arm.Instances.update_sha3_224 },
  Spec.Sha3.finalizeSha3_224Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Instances.finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len
    stack := 664
    verified := Proof.Sha3.Arm.Instances.finalize_sha3_224 },
  Spec.Sha3.updateSha3_256Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Instances.update Spec.Sha3.hashSha3_256.rate
    stack := 16
    verified := Proof.Sha3.Arm.Instances.update_sha3_256 },
  Spec.Sha3.finalizeSha3_256Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Instances.finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len
    stack := 664
    verified := Proof.Sha3.Arm.Instances.finalize_sha3_256 },
  Spec.Sha3.updateSha3_384Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Instances.update Spec.Sha3.hashSha3_384.rate
    stack := 16
    verified := Proof.Sha3.Arm.Instances.update_sha3_384 },
  Spec.Sha3.finalizeSha3_384Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Instances.finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len
    stack := 664
    verified := Proof.Sha3.Arm.Instances.finalize_sha3_384 },
  Spec.Sha3.updateSha3_512Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Instances.update Spec.Sha3.hashSha3_512.rate
    stack := 16
    verified := Proof.Sha3.Arm.Instances.update_sha3_512 },
  Spec.Sha3.finalizeSha3_512Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Instances.finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len
    stack := 664
    verified := Proof.Sha3.Arm.Instances.finalize_sha3_512 },
  Spec.Sha3.updateShake128Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Instances.update Spec.Sha3.xofShake128.rate
    stack := 16
    verified := Proof.Sha3.Arm.Instances.update_shake128 },
  Spec.Sha3.finalizeShake128Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Instances.xofFinalize Spec.Sha3.xofShake128.rate
    stack := 648
    verified := Proof.Sha3.Arm.Instances.finalize_shake128 },
  Spec.Sha3.squeezeShake128Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Instances.xofSqueeze Spec.Sha3.xofShake128.rate
    stack := 656
    verified := Proof.Sha3.Arm.Instances.squeeze_shake128 },
  Spec.Sha3.finalizeShake256Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Instances.xofFinalize Spec.Sha3.xofShake256.rate
    stack := 648
    verified := Proof.Sha3.Arm.Instances.finalize_shake256 },
  Spec.Sha3.squeezeShake256Api.artifact Arm.target {
    code := Impl.Sha3.Arm.Instances.xofSqueeze Spec.Sha3.xofShake256.rate
    stack := 656
    verified := Proof.Sha3.Arm.Instances.squeeze_shake256 }]

end VG.Artifacts.Sha3.Arm
