module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sha3.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # SHA-3 and SHAKE (FIPS 202) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sha3.RISCV64

def artifacts : List Artifact := [
  Spec.Sha3.updateSha3_224Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Fn.update Spec.Sha3.hashSha3_224.rate
    verified := .scrubbed Proof.Sha3.RISCV64.update_sha3_224_scrubbed },
  Spec.Sha3.finalizeSha3_224Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Fn.finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len
    verified := .scrubbed Proof.Sha3.RISCV64.finalize_sha3_224_scrubbed },
  Spec.Sha3.updateSha3_256Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Fn.update Spec.Sha3.hashSha3_256.rate
    verified := .scrubbed Proof.Sha3.RISCV64.update_sha3_256_scrubbed },
  Spec.Sha3.finalizeSha3_256Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Fn.finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len
    verified := .scrubbed Proof.Sha3.RISCV64.finalize_sha3_256_scrubbed },
  Spec.Sha3.updateSha3_384Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Fn.update Spec.Sha3.hashSha3_384.rate
    verified := .scrubbed Proof.Sha3.RISCV64.update_sha3_384_scrubbed },
  Spec.Sha3.finalizeSha3_384Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Fn.finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len
    verified := .scrubbed Proof.Sha3.RISCV64.finalize_sha3_384_scrubbed },
  Spec.Sha3.updateSha3_512Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Fn.update Spec.Sha3.hashSha3_512.rate
    verified := .scrubbed Proof.Sha3.RISCV64.update_sha3_512_scrubbed },
  Spec.Sha3.finalizeSha3_512Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Fn.finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len
    verified := .scrubbed Proof.Sha3.RISCV64.finalize_sha3_512_scrubbed },
  Spec.Sha3.updateShake128Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Fn.update Spec.Sha3.xofShake128.rate
    verified := .scrubbed Proof.Sha3.RISCV64.update_shake128_scrubbed },
  Spec.Sha3.finalizeShake128Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Fn.xofFinalize Spec.Sha3.xofShake128.rate
    verified := .scrubbed Proof.Sha3.RISCV64.finalize_shake128_scrubbed },
  Spec.Sha3.squeezeShake128Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Fn.xofSqueeze Spec.Sha3.xofShake128.rate
    verified := .scrubbed Proof.Sha3.RISCV64.squeeze_shake128_scrubbed },
  Spec.Sha3.finalizeShake256Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Fn.xofFinalize Spec.Sha3.xofShake256.rate
    verified := .scrubbed Proof.Sha3.RISCV64.finalize_shake256_scrubbed },
  Spec.Sha3.squeezeShake256Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Fn.xofSqueeze Spec.Sha3.xofShake256.rate
    verified := .scrubbed Proof.Sha3.RISCV64.squeeze_shake256_scrubbed }]

end VG.Artifacts.Sha3.RISCV64
