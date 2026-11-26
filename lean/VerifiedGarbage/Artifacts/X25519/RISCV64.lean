module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Proof.X25519.RISCV64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # X25519 (RFC 7748) on RISC-V -/

namespace VG.Artifacts.X25519.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.X25519.exchangeApi.artifact RISCV64.target {
    code := Impl.X25519.RISCV64.Fn.exchange
    verified := Proof.X25519.RISCV64.Scrub.exchange_scrubbed },
  Spec.X25519.x25519BaseApi.artifact RISCV64.target {
    code := Impl.X25519.RISCV64.Fn.base
    verified := Proof.X25519.RISCV64.Scrub.base_scrubbed }]

spec_apis artifacts

end VG.Artifacts.X25519.RISCV64
