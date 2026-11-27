module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sha256.Contract
import VerifiedGarbage.Proof.Sha256.RISCV64.Scrub
import VerifiedGarbage.Impl.Sha256.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SHA-256 (FIPS 180-4) on RISC-V -/

namespace VG.Artifacts.Sha256.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Sha256.init224Api.artifact RISCV64.target {
    code := Impl.Sha256.RISCV64.Fn.init224
    verified := Proof.Sha256.RISCV64.init224_scrubbed },
  Spec.Sha256.finalize224Api.artifact RISCV64.target {
    code := Impl.Sha256.RISCV64.Fn.finalize224
    verified := Proof.Sha256.RISCV64.finalize224_scrubbed },
  Spec.Sha256.digest224Api.artifact RISCV64.target {
    code := Impl.Sha256.RISCV64.Fn.digest224
    verified := Proof.Sha256.RISCV64.digest224_scrubbed },
  Spec.Sha256.initApi.artifact RISCV64.target {
    code := Impl.Sha256.RISCV64.Fn.init
    verified := Proof.Sha256.RISCV64.init_scrubbed },
  Spec.Sha256.updateApi.artifact RISCV64.target {
    code := Impl.Sha256.RISCV64.Fn.update
    verified := Proof.Sha256.RISCV64.update_scrubbed },
  Spec.Sha256.finalizeApi.artifact RISCV64.target {
    code := Impl.Sha256.RISCV64.Fn.finalize
    verified := Proof.Sha256.RISCV64.finalize_scrubbed },
  Spec.Sha256.digest256Api.artifact RISCV64.target {
    code := Impl.Sha256.RISCV64.Fn.digest
    verified := Proof.Sha256.RISCV64.digest_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sha256.RISCV64
