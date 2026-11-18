module

public import VerifiedGarbage.Proof.Cast5.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Cast5.RISCV64.ModesLit

/-! # CAST5-CBC on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Cast5Cbc.RISCV64

def artifacts : List Artifact := [
  Spec.Cast5.cbcEncryptChainedApi.artifact RISCV64.target Proof.Cast5.RISCV64.Scrub.cbcEncryptChainedReg,
  Spec.Cast5.cbcDecryptChainedApi.artifact RISCV64.target Proof.Cast5.RISCV64.Scrub.cbcDecryptChainedReg]

end VG.Artifacts.Cast5Cbc.RISCV64
