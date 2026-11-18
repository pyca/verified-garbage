module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sm3.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # SM3 (GB/T 32905-2016) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm3.RISCV64

def artifacts : List Artifact := [
  Spec.Sm3.initApi.artifact RISCV64.target Proof.Sm3.RISCV64.initReg,
  Spec.Sm3.updateApi.artifact RISCV64.target Proof.Sm3.RISCV64.updateReg,
  Spec.Sm3.finalizeApi.artifact RISCV64.target Proof.Sm3.RISCV64.finalizeReg]

end VG.Artifacts.Sm3.RISCV64
