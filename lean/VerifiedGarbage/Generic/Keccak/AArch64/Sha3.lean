module

public import VerifiedGarbage.Proof.Sha3.AArch64.Instances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # SHA-3 and SHAKE (FIPS 202) on AArch64 -/

@[expose] public section

namespace VG.Generic.Keccak.AArch64.Sha3

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  Spec.Sha3.updateSha3_224Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.Sha3.AArch64.Instances.update v.callee Spec.Sha3.hashSha3_224.rate
    stack := 16
    verified := Proof.Sha3.AArch64.Instances.update_sha3_224 v },
  Spec.Sha3.finalizeSha3_224Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.Sha3.AArch64.Instances.finalize v.callee Spec.Sha3.hashSha3_224.rate
      Spec.Sha3.hashSha3_224.len
    stack := 16 + 672
    verified := Proof.Sha3.AArch64.Instances.finalize_sha3_224 v },
  Spec.Sha3.updateSha3_256Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.Sha3.AArch64.Instances.update v.callee Spec.Sha3.hashSha3_256.rate
    stack := 16
    verified := Proof.Sha3.AArch64.Instances.update_sha3_256 v },
  Spec.Sha3.finalizeSha3_256Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.Sha3.AArch64.Instances.finalize v.callee Spec.Sha3.hashSha3_256.rate
      Spec.Sha3.hashSha3_256.len
    stack := 16 + 672
    verified := Proof.Sha3.AArch64.Instances.finalize_sha3_256 v },
  Spec.Sha3.updateSha3_384Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.Sha3.AArch64.Instances.update v.callee Spec.Sha3.hashSha3_384.rate
    stack := 16
    verified := Proof.Sha3.AArch64.Instances.update_sha3_384 v },
  Spec.Sha3.finalizeSha3_384Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.Sha3.AArch64.Instances.finalize v.callee Spec.Sha3.hashSha3_384.rate
      Spec.Sha3.hashSha3_384.len
    stack := 16 + 672
    verified := Proof.Sha3.AArch64.Instances.finalize_sha3_384 v },
  Spec.Sha3.updateSha3_512Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.Sha3.AArch64.Instances.update v.callee Spec.Sha3.hashSha3_512.rate
    stack := 16
    verified := Proof.Sha3.AArch64.Instances.update_sha3_512 v },
  Spec.Sha3.finalizeSha3_512Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.Sha3.AArch64.Instances.finalize v.callee Spec.Sha3.hashSha3_512.rate
      Spec.Sha3.hashSha3_512.len
    stack := 16 + 672
    verified := Proof.Sha3.AArch64.Instances.finalize_sha3_512 v },
  Spec.Sha3.updateShake128Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.Sha3.AArch64.Instances.update v.callee Spec.Sha3.xofShake128.rate
    stack := 16
    verified := Proof.Sha3.AArch64.Instances.update_shake128 v },
  Spec.Sha3.finalizeShake128Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.Sha3.AArch64.Instances.xofFinalize v.callee Spec.Sha3.xofShake128.rate
    stack := 16 + 640
    verified := Proof.Sha3.AArch64.Instances.finalize_shake128 v },
  Spec.Sha3.squeezeShake128Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.Sha3.AArch64.Instances.xofSqueeze v.callee Spec.Sha3.xofShake128.rate
    stack := 16 + 640
    verified := Proof.Sha3.AArch64.Instances.squeeze_shake128 v },
  Spec.Sha3.finalizeShake256Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.Sha3.AArch64.Instances.xofFinalize v.callee Spec.Sha3.xofShake256.rate
    stack := 16 + 640
    verified := Proof.Sha3.AArch64.Instances.finalize_shake256 v },
  Spec.Sha3.squeezeShake256Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.Sha3.AArch64.Instances.xofSqueeze v.callee Spec.Sha3.xofShake256.rate
    stack := 16 + 640
    verified := Proof.Sha3.AArch64.Instances.squeeze_shake256 v }]

end VG.Generic.Keccak.AArch64.Sha3
