module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sha256.RISCV64.Scrub
public import VerifiedGarbage.Impl.Sha256.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # SHA-256 (FIPS 180-4) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sha256.RISCV64

def artifacts : List Artifact := [
  Spec.Sha256.init224Api.artifact RISCV64.target {
    code := Impl.Sha256.RISCV64.Fn.init224
    verified := .scrubbed Proof.Sha256.RISCV64.init224_scrubbed },
  Spec.Sha256.finalize224Api.artifact RISCV64.target {
    code := Impl.Sha256.RISCV64.Fn.finalize224
    verified := .scrubbed Proof.Sha256.RISCV64.finalize224_scrubbed },
  Spec.Sha256.digest224Api.artifact RISCV64.target {
    code := Impl.Sha256.RISCV64.Fn.digest224
    verified := .scrubbed Proof.Sha256.RISCV64.digest224_scrubbed },
  Spec.Sha256.initApi.artifact RISCV64.target {
    code := Impl.Sha256.RISCV64.Fn.init
    verified := .scrubbed Proof.Sha256.RISCV64.init_scrubbed },
  Spec.Sha256.updateApi.artifact RISCV64.target {
    code := Impl.Sha256.RISCV64.Fn.update
    verified := .scrubbed Proof.Sha256.RISCV64.update_scrubbed },
  Spec.Sha256.finalizeApi.artifact RISCV64.target {
    code := Impl.Sha256.RISCV64.Fn.finalize
    verified := .scrubbed Proof.Sha256.RISCV64.finalize_scrubbed },
  Spec.Sha256.digest256Api.artifact RISCV64.target {
    code := Impl.Sha256.RISCV64.Fn.digest
    verified := .scrubbed Proof.Sha256.RISCV64.digest_scrubbed }]

end VG.Artifacts.Sha256.RISCV64
