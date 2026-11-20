module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sha512.RISCV64.Scrub
public import VerifiedGarbage.Impl.Sha512.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sha512.RISCV64

def artifacts : List Artifact := [
  Spec.Sha512.init384Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Fn.init384
    verified := .scrubbed Proof.Sha512.RISCV64.init384_scrubbed },
  Spec.Sha512.init512Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Fn.init512
    verified := .scrubbed Proof.Sha512.RISCV64.init512_scrubbed },
  Spec.Sha512.init512_224Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Fn.init512_224
    verified := .scrubbed Proof.Sha512.RISCV64.init512_224_scrubbed },
  Spec.Sha512.init512_256Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Fn.init512_256
    verified := .scrubbed Proof.Sha512.RISCV64.init512_256_scrubbed },
  Spec.Sha512.updateApi.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Fn.update
    verified := .scrubbed Proof.Sha512.RISCV64.update_scrubbed },
  Spec.Sha512.finalizeApi.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Fn.finalize
    verified := .scrubbed Proof.Sha512.RISCV64.finalize_scrubbed },
  Spec.Sha512.finalize384Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Fn.finalize384
    verified := .scrubbed Proof.Sha512.RISCV64.finalize384_scrubbed },
  Spec.Sha512.finalize512_256Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Fn.finalize512_256
    verified := .scrubbed Proof.Sha512.RISCV64.finalize512_256_scrubbed },
  Spec.Sha512.finalize512_224Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Fn.finalize512_224
    verified := .scrubbed Proof.Sha512.RISCV64.finalize512_224_scrubbed },
  Spec.Sha512.digest384Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Fn.digest384
    verified := .scrubbed Proof.Sha512.RISCV64.digest384_scrubbed },
  Spec.Sha512.digest512Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Fn.digest512
    verified := .scrubbed Proof.Sha512.RISCV64.digest512_scrubbed },
  Spec.Sha512.digest512_224Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Fn.digest512_224
    verified := .scrubbed Proof.Sha512.RISCV64.digest512_224_scrubbed },
  Spec.Sha512.digest512_256Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Fn.digest512_256
    verified := .scrubbed Proof.Sha512.RISCV64.digest512_256_scrubbed }]

end VG.Artifacts.Sha512.RISCV64
