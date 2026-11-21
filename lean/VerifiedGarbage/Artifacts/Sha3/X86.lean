module

public import VerifiedGarbage.Proof.Sha3.X86.Absorb
public import VerifiedGarbage.Proof.Sha3.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Sha3.X86.Lit

/-! # SHA-3 and SHAKE (FIPS 202) on x86 -/

@[expose] public section

namespace VG.Artifacts.Sha3.X86

def artifacts : List Artifact := [
  Spec.Sha3.updateSha3_224Api.artifact X86.target {
    code := Impl.Sha3.X86.Fn.update Spec.Sha3.hashSha3_224.rate
    verified := Proof.Sha3.X86.Absorb.update_sha3_224_scrubbed },
  Spec.Sha3.finalizeSha3_224Api.artifact X86.target {
    code := Impl.Sha3.X86.Fn.finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len
    verified := Proof.Sha3.X86.Scrub.finalize_sha3_224_scrubbed },
  Spec.Sha3.updateSha3_256Api.artifact X86.target {
    code := Impl.Sha3.X86.Fn.update Spec.Sha3.hashSha3_256.rate
    verified := Proof.Sha3.X86.Absorb.update_sha3_256_scrubbed },
  Spec.Sha3.finalizeSha3_256Api.artifact X86.target {
    code := Impl.Sha3.X86.Fn.finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len
    verified := Proof.Sha3.X86.Scrub.finalize_sha3_256_scrubbed },
  Spec.Sha3.updateSha3_384Api.artifact X86.target {
    code := Impl.Sha3.X86.Fn.update Spec.Sha3.hashSha3_384.rate
    verified := Proof.Sha3.X86.Absorb.update_sha3_384_scrubbed },
  Spec.Sha3.finalizeSha3_384Api.artifact X86.target {
    code := Impl.Sha3.X86.Fn.finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len
    verified := Proof.Sha3.X86.Scrub.finalize_sha3_384_scrubbed },
  Spec.Sha3.updateSha3_512Api.artifact X86.target {
    code := Impl.Sha3.X86.Fn.update Spec.Sha3.hashSha3_512.rate
    verified := Proof.Sha3.X86.Absorb.update_sha3_512_scrubbed },
  Spec.Sha3.finalizeSha3_512Api.artifact X86.target {
    code := Impl.Sha3.X86.Fn.finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len
    verified := Proof.Sha3.X86.Scrub.finalize_sha3_512_scrubbed },
  Spec.Sha3.updateShake128Api.artifact X86.target {
    code := Impl.Sha3.X86.Fn.update Spec.Sha3.xofShake128.rate
    verified := Proof.Sha3.X86.Absorb.update_shake128_scrubbed },
  Spec.Sha3.finalizeShake128Api.artifact X86.target {
    code := Impl.Sha3.X86.Fn.xofFinalize Spec.Sha3.xofShake128.rate
    verified := Proof.Sha3.X86.Scrub.finalize_shake128_scrubbed },
  Spec.Sha3.squeezeShake128Api.artifact X86.target {
    code := Impl.Sha3.X86.Fn.xofSqueeze Spec.Sha3.xofShake128.rate
    verified := Proof.Sha3.X86.Scrub.squeeze_shake128_scrubbed },
  Spec.Sha3.finalizeShake256Api.artifact X86.target {
    code := Impl.Sha3.X86.Fn.xofFinalize Spec.Sha3.xofShake256.rate
    verified := Proof.Sha3.X86.Scrub.finalize_shake256_scrubbed },
  Spec.Sha3.squeezeShake256Api.artifact X86.target {
    code := Impl.Sha3.X86.Fn.xofSqueeze Spec.Sha3.xofShake256.rate
    verified := Proof.Sha3.X86.Scrub.squeeze_shake256_scrubbed }]

end VG.Artifacts.Sha3.X86
