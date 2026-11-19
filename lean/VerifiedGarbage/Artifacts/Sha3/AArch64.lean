module

public import VerifiedGarbage.Proof.Sha3.AArch64.Instances
public import VerifiedGarbage.Proof.Sha3.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.Keccak.AArch64

/-! # SHA-3 and SHAKE (FIPS 202) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sha3.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.Keccak.AArch64.variants.flatMap fun (v : Proof.Sha3.AArch64.Permutation) => [
    Spec.Sha3.updateSha3_224Api.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
      suffix := v.callee.suffix
      vendor := v.vendor
      code := Impl.Sha3.AArch64.Instances.update v.callee Spec.Sha3.hashSha3_224.rate
      verified := Proof.Sha3.AArch64.Instances.update_sha3_224 v }
      (Proof.Sha3.AArch64.Scrub.updateOk Spec.Sha3.hashSha3_224.rate 16)),
    Spec.Sha3.absorbSha3_224Api.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
      suffix := v.callee.suffix
      vendor := v.vendor
      code := Impl.Sha3.AArch64.Instances.absorb v.callee Spec.Sha3.hashSha3_224.rate
      verified := Proof.Sha3.AArch64.Instances.absorb_sha3_224 v }
      (Proof.Sha3.AArch64.Scrub.absorbOk Spec.Sha3.hashSha3_224.rate 656)),
    Spec.Sha3.finalizeSha3_224Api.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
      suffix := v.callee.suffix
      vendor := v.vendor
      code := Impl.Sha3.AArch64.Instances.finalize v.callee Spec.Sha3.hashSha3_224.rate
        Spec.Sha3.hashSha3_224.len
      verified := Proof.Sha3.AArch64.Instances.finalize_sha3_224 v }
      (Proof.Sha3.AArch64.Scrub.finalizeOk Spec.Sha3.hashSha3_224 (16 + 672))),
    Spec.Sha3.updateSha3_256Api.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
      suffix := v.callee.suffix
      vendor := v.vendor
      code := Impl.Sha3.AArch64.Instances.update v.callee Spec.Sha3.hashSha3_256.rate
      verified := Proof.Sha3.AArch64.Instances.update_sha3_256 v }
      (Proof.Sha3.AArch64.Scrub.updateOk Spec.Sha3.hashSha3_256.rate 16)),
    Spec.Sha3.absorbSha3_256Api.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
      suffix := v.callee.suffix
      vendor := v.vendor
      code := Impl.Sha3.AArch64.Instances.absorb v.callee Spec.Sha3.hashSha3_256.rate
      verified := Proof.Sha3.AArch64.Instances.absorb_sha3_256 v }
      (Proof.Sha3.AArch64.Scrub.absorbOk Spec.Sha3.hashSha3_256.rate 656)),
    Spec.Sha3.finalizeSha3_256Api.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
      suffix := v.callee.suffix
      vendor := v.vendor
      code := Impl.Sha3.AArch64.Instances.finalize v.callee Spec.Sha3.hashSha3_256.rate
        Spec.Sha3.hashSha3_256.len
      verified := Proof.Sha3.AArch64.Instances.finalize_sha3_256 v }
      (Proof.Sha3.AArch64.Scrub.finalizeOk Spec.Sha3.hashSha3_256 (16 + 672))),
    Spec.Sha3.updateSha3_384Api.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
      suffix := v.callee.suffix
      vendor := v.vendor
      code := Impl.Sha3.AArch64.Instances.update v.callee Spec.Sha3.hashSha3_384.rate
      verified := Proof.Sha3.AArch64.Instances.update_sha3_384 v }
      (Proof.Sha3.AArch64.Scrub.updateOk Spec.Sha3.hashSha3_384.rate 16)),
    Spec.Sha3.absorbSha3_384Api.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
      suffix := v.callee.suffix
      vendor := v.vendor
      code := Impl.Sha3.AArch64.Instances.absorb v.callee Spec.Sha3.hashSha3_384.rate
      verified := Proof.Sha3.AArch64.Instances.absorb_sha3_384 v }
      (Proof.Sha3.AArch64.Scrub.absorbOk Spec.Sha3.hashSha3_384.rate 656)),
    Spec.Sha3.finalizeSha3_384Api.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
      suffix := v.callee.suffix
      vendor := v.vendor
      code := Impl.Sha3.AArch64.Instances.finalize v.callee Spec.Sha3.hashSha3_384.rate
        Spec.Sha3.hashSha3_384.len
      verified := Proof.Sha3.AArch64.Instances.finalize_sha3_384 v }
      (Proof.Sha3.AArch64.Scrub.finalizeOk Spec.Sha3.hashSha3_384 (16 + 672))),
    Spec.Sha3.updateSha3_512Api.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
      suffix := v.callee.suffix
      vendor := v.vendor
      code := Impl.Sha3.AArch64.Instances.update v.callee Spec.Sha3.hashSha3_512.rate
      verified := Proof.Sha3.AArch64.Instances.update_sha3_512 v }
      (Proof.Sha3.AArch64.Scrub.updateOk Spec.Sha3.hashSha3_512.rate 16)),
    Spec.Sha3.absorbSha3_512Api.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
      suffix := v.callee.suffix
      vendor := v.vendor
      code := Impl.Sha3.AArch64.Instances.absorb v.callee Spec.Sha3.hashSha3_512.rate
      verified := Proof.Sha3.AArch64.Instances.absorb_sha3_512 v }
      (Proof.Sha3.AArch64.Scrub.absorbOk Spec.Sha3.hashSha3_512.rate 656)),
    Spec.Sha3.finalizeSha3_512Api.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
      suffix := v.callee.suffix
      vendor := v.vendor
      code := Impl.Sha3.AArch64.Instances.finalize v.callee Spec.Sha3.hashSha3_512.rate
        Spec.Sha3.hashSha3_512.len
      verified := Proof.Sha3.AArch64.Instances.finalize_sha3_512 v }
      (Proof.Sha3.AArch64.Scrub.finalizeOk Spec.Sha3.hashSha3_512 (16 + 672))),
    Spec.Sha3.updateShake128Api.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
      suffix := v.callee.suffix
      vendor := v.vendor
      code := Impl.Sha3.AArch64.Instances.update v.callee Spec.Sha3.xofShake128.rate
      verified := Proof.Sha3.AArch64.Instances.update_shake128 v }
      (Proof.Sha3.AArch64.Scrub.updateOk Spec.Sha3.xofShake128.rate 16)),
    Spec.Sha3.absorbShake128Api.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
      suffix := v.callee.suffix
      vendor := v.vendor
      code := Impl.Sha3.AArch64.Instances.absorb v.callee Spec.Sha3.xofShake128.rate
      verified := Proof.Sha3.AArch64.Instances.absorb_shake128 v }
      (Proof.Sha3.AArch64.Scrub.absorbOk Spec.Sha3.xofShake128.rate 656)),
    Spec.Sha3.finalizeShake128Api.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
      suffix := v.callee.suffix
      vendor := v.vendor
      code := Impl.Sha3.AArch64.Instances.xofFinalize v.callee Spec.Sha3.xofShake128.rate
      verified := Proof.Sha3.AArch64.Instances.finalize_shake128 v }
      (Proof.Sha3.AArch64.Scrub.xofFinalizeOk Spec.Sha3.xofShake128 (16 + 640))),
    Spec.Sha3.squeezeShake128Api.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
      suffix := v.callee.suffix
      vendor := v.vendor
      code := Impl.Sha3.AArch64.Instances.xofSqueeze v.callee Spec.Sha3.xofShake128.rate
      verified := Proof.Sha3.AArch64.Instances.squeeze_shake128 v }
      (Proof.Sha3.AArch64.Scrub.xofSqueezeOk Spec.Sha3.xofShake128 (16 + 640))),
    Spec.Sha3.finalizeShake256Api.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
      suffix := v.callee.suffix
      vendor := v.vendor
      code := Impl.Sha3.AArch64.Instances.xofFinalize v.callee Spec.Sha3.xofShake256.rate
      verified := Proof.Sha3.AArch64.Instances.finalize_shake256 v }
      (Proof.Sha3.AArch64.Scrub.xofFinalizeOk Spec.Sha3.xofShake256 (16 + 640))),
    Spec.Sha3.squeezeShake256Api.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
      suffix := v.callee.suffix
      vendor := v.vendor
      code := Impl.Sha3.AArch64.Instances.xofSqueeze v.callee Spec.Sha3.xofShake256.rate
      verified := Proof.Sha3.AArch64.Instances.squeeze_shake256 v }
      (Proof.Sha3.AArch64.Scrub.xofSqueezeOk Spec.Sha3.xofShake256 (16 + 640)))]

end VG.Artifacts.Sha3.AArch64
