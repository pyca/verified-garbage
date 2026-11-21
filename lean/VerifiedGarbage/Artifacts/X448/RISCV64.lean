module

public import VerifiedGarbage.Proof.X448.RISCV64.Scrub
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # X448 (RFC 7748) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.X448.RISCV64

def artifacts : List Artifact := [
  Spec.X448.exchangeApi.artifact RISCV64.target {
    code := Impl.X448.RISCV64.Fn.exchange
    verified := Proof.X448.RISCV64.Scrub.exchange_scrubbed },
  Spec.X448.x448BaseApi.artifact RISCV64.target {
    code := Impl.X448.RISCV64.Fn.base
    verified := Proof.X448.RISCV64.Scrub.base_scrubbed }]

end VG.Artifacts.X448.RISCV64
