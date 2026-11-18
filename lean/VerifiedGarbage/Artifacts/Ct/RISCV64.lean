module

public import VerifiedGarbage.Proof.Ct.RISCV64Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # Constant-time byte comparison on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ct.RISCV64

def artifacts : List Artifact := [
  Spec.Ct.eqApi.artifact RISCV64.target Proof.Ct.RISCV64Scrub.eqReg]

end VG.Artifacts.Ct.RISCV64
