module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Proof.X448.RISCV64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # X448 (RFC 7748) on RISC-V -/

namespace VG.Artifacts.X448.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.X448.exchangeApi.artifact RISCV64.target {
    code := Impl.X448.RISCV64.Fn.exchange
    verified := Proof.X448.RISCV64.Scrub.exchange_scrubbed },
  Spec.X448.x448BaseApi.artifact RISCV64.target {
    code := Impl.X448.RISCV64.Fn.base
    verified := Proof.X448.RISCV64.Scrub.base_scrubbed }]

spec_apis artifacts

end VG.Artifacts.X448.RISCV64
