module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sha3.Instances
import VerifiedGarbage.Proof.Sha3.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SHA-3 and SHAKE (FIPS 202) on PPC64LE -/

namespace VG.Artifacts.Sha3.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Sha3.updateSha3_224Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Fn.update Spec.Sha3.hashSha3_224.rate
    verified := Proof.Sha3.PPC64LE.Scrub.update_sha3_224_scrubbed },
  Spec.Sha3.finalizeSha3_224Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Fn.finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len
    verified := Proof.Sha3.PPC64LE.Scrub.finalize_sha3_224_scrubbed },
  Spec.Sha3.updateSha3_256Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Fn.update Spec.Sha3.hashSha3_256.rate
    verified := Proof.Sha3.PPC64LE.Scrub.update_sha3_256_scrubbed },
  Spec.Sha3.finalizeSha3_256Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Fn.finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len
    verified := Proof.Sha3.PPC64LE.Scrub.finalize_sha3_256_scrubbed },
  Spec.Sha3.updateSha3_384Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Fn.update Spec.Sha3.hashSha3_384.rate
    verified := Proof.Sha3.PPC64LE.Scrub.update_sha3_384_scrubbed },
  Spec.Sha3.finalizeSha3_384Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Fn.finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len
    verified := Proof.Sha3.PPC64LE.Scrub.finalize_sha3_384_scrubbed },
  Spec.Sha3.updateSha3_512Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Fn.update Spec.Sha3.hashSha3_512.rate
    verified := Proof.Sha3.PPC64LE.Scrub.update_sha3_512_scrubbed },
  Spec.Sha3.finalizeSha3_512Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Fn.finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len
    verified := Proof.Sha3.PPC64LE.Scrub.finalize_sha3_512_scrubbed },
  Spec.Sha3.updateShake128Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Fn.update Spec.Sha3.xofShake128.rate
    verified := Proof.Sha3.PPC64LE.Scrub.update_shake128_scrubbed },
  Spec.Sha3.finalizeShake128Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Fn.xofFinalize Spec.Sha3.xofShake128.rate
    verified := Proof.Sha3.PPC64LE.Scrub.finalize_shake128_scrubbed },
  Spec.Sha3.squeezeShake128Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Fn.xofSqueeze Spec.Sha3.xofShake128.rate
    verified := Proof.Sha3.PPC64LE.Scrub.squeeze_shake128_scrubbed },
  Spec.Sha3.finalizeShake256Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Fn.xofFinalize Spec.Sha3.xofShake256.rate
    verified := Proof.Sha3.PPC64LE.Scrub.finalize_shake256_scrubbed },
  Spec.Sha3.squeezeShake256Api.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Fn.xofSqueeze Spec.Sha3.xofShake256.rate
    verified := Proof.Sha3.PPC64LE.Scrub.squeeze_shake256_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sha3.PPC64LE
