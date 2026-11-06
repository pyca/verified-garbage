module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.X25519.RISCV64.R64.Verified
public import VerifiedGarbage.Proof.X25519.RISCV64.BaseVerified
public import VerifiedGarbage.Proof.X25519.RISCV64.Exchange
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # X25519 (RFC 7748) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.X25519.RISCV64

def artifacts : List Artifact := [
  Spec.X25519.exchangeApi.artifact RISCV64.target {
    code := Impl.Xdh.RISCV64.exchange "vg_x25519" Impl.X25519.RISCV64.R64.x25519 32
    stack := 16
    verified := Proof.X25519.RISCV64.Exchange.exchange_verified },
  Spec.X25519.x25519BaseApi.artifact RISCV64.target {
    code := Impl.X25519.RISCV64.Base.x25519Base
    verified := Proof.X25519.RISCV64.Base.x25519Base_verified }]

end VG.Artifacts.X25519.RISCV64
