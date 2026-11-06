module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Verified
public import VerifiedGarbage.Proof.X448.RISCV64.Exchange
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # X448 (RFC 7748) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.X448.RISCV64

def artifacts : List Artifact := [
  Spec.X448.exchangeApi.artifact RISCV64.target {
    code := Impl.Xdh.RISCV64.exchange "vg_x448" Impl.X448.RISCV64.R64.x448 56
    stack := 16
    verified := Proof.X448.RISCV64.Exchange.exchange_verified },
  Spec.X448.x448BaseApi.artifact RISCV64.target {
    code := Impl.X448.RISCV64.R64.x448Base
    verified := Proof.X448.RISCV64.R64.x448Base_verified }]

end VG.Artifacts.X448.RISCV64
