module

public import VerifiedGarbage.Proof.X448.RISCV64.Scrub
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # X448 (RFC 7748) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.X448.RISCV64

def artifacts : List Artifact := [
  Spec.X448.exchangeApi.artifact RISCV64.target Proof.X448.RISCV64.Scrub.exchangeReg,
  Spec.X448.x448BaseApi.artifact RISCV64.target Proof.X448.RISCV64.Scrub.baseReg]

end VG.Artifacts.X448.RISCV64
