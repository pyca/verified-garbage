module

public import VerifiedGarbage.Proof.Sm4.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit

/-! # SM4-CTR on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm4Ctr.RISCV64

def artifacts : List Artifact := [
  Spec.Sm4.ctrApi.artifact RISCV64.target Proof.Sm4.RISCV64.Scrub.ctrReg,
  Spec.Sm4.ctrFinalApi.artifact RISCV64.target Proof.Sm4.RISCV64.Scrub.ctrFinalReg]

end VG.Artifacts.Sm4Ctr.RISCV64
