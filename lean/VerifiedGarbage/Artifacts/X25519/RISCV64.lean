module

public import VerifiedGarbage.Proof.X25519.RISCV64.Scrub
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # X25519 (RFC 7748) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.X25519.RISCV64

def artifacts : List Artifact := [
  Spec.X25519.exchangeApi.artifact RISCV64.target Proof.X25519.RISCV64.Scrub.exchangeReg,
  Spec.X25519.x25519BaseApi.artifact RISCV64.target Proof.X25519.RISCV64.Scrub.baseReg]

end VG.Artifacts.X25519.RISCV64
