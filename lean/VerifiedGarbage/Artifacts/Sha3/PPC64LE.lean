module

public import VerifiedGarbage.Proof.Sha3.PPC64LE.Instances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # SHA-3 and SHAKE (FIPS 202) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sha3.PPC64LE

def artifacts : List Artifact := [
  Spec.Sha3.updateSha3_224Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Instances.update Spec.Sha3.hashSha3_224.rate
    stack := 48
    verified := Proof.Sha3.PPC64LE.Instances.update_sha3_224 },
  Spec.Sha3.finalizeSha3_224Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Instances.finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len
    stack := 48 + 704
    verified := Proof.Sha3.PPC64LE.Instances.finalize_sha3_224 },
  Spec.Sha3.updateSha3_256Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Instances.update Spec.Sha3.hashSha3_256.rate
    stack := 48
    verified := Proof.Sha3.PPC64LE.Instances.update_sha3_256 },
  Spec.Sha3.finalizeSha3_256Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Instances.finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len
    stack := 48 + 704
    verified := Proof.Sha3.PPC64LE.Instances.finalize_sha3_256 },
  Spec.Sha3.updateSha3_384Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Instances.update Spec.Sha3.hashSha3_384.rate
    stack := 48
    verified := Proof.Sha3.PPC64LE.Instances.update_sha3_384 },
  Spec.Sha3.finalizeSha3_384Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Instances.finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len
    stack := 48 + 704
    verified := Proof.Sha3.PPC64LE.Instances.finalize_sha3_384 },
  Spec.Sha3.updateSha3_512Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Instances.update Spec.Sha3.hashSha3_512.rate
    stack := 48
    verified := Proof.Sha3.PPC64LE.Instances.update_sha3_512 },
  Spec.Sha3.finalizeSha3_512Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Instances.finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len
    stack := 48 + 704
    verified := Proof.Sha3.PPC64LE.Instances.finalize_sha3_512 },
  Spec.Sha3.updateShake128Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Instances.update Spec.Sha3.xofShake128.rate
    stack := 48
    verified := Proof.Sha3.PPC64LE.Instances.update_shake128 },
  Spec.Sha3.finalizeShake128Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Instances.xofFinalize Spec.Sha3.xofShake128.rate
    stack := 48 + 672
    verified := Proof.Sha3.PPC64LE.Instances.finalize_shake128 },
  Spec.Sha3.squeezeShake128Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Instances.xofSqueeze Spec.Sha3.xofShake128.rate
    stack := 48 + 672
    verified := Proof.Sha3.PPC64LE.Instances.squeeze_shake128 },
  Spec.Sha3.finalizeShake256Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Instances.xofFinalize Spec.Sha3.xofShake256.rate
    stack := 48 + 672
    verified := Proof.Sha3.PPC64LE.Instances.finalize_shake256 },
  Spec.Sha3.squeezeShake256Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Instances.xofSqueeze Spec.Sha3.xofShake256.rate
    stack := 48 + 672
    verified := Proof.Sha3.PPC64LE.Instances.squeeze_shake256 }]

end VG.Artifacts.Sha3.PPC64LE
