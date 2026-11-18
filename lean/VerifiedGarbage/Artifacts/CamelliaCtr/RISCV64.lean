module

public import VerifiedGarbage.Proof.Camellia.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit

/-! # Camellia-CTR on RISC-V -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.RISCV64

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact RISCV64.target Proof.Camellia.RISCV64.Scrub.ctrReg,
  Spec.Camellia.ctrFinalApi.artifact RISCV64.target Proof.Camellia.RISCV64.Scrub.ctrFinalReg]

end VG.Artifacts.CamelliaCtr.RISCV64
