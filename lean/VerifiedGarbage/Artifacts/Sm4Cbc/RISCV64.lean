module

public import VerifiedGarbage.Proof.Sm4.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit

/-! # SM4-CBC on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm4Cbc.RISCV64

def artifacts : List Artifact := [
  Spec.Sm4.cbcEncryptChainedApi.artifact RISCV64.target Proof.Sm4.RISCV64.Scrub.cbcEncryptChainedReg,
  Spec.Sm4.cbcDecryptChainedApi.artifact RISCV64.target Proof.Sm4.RISCV64.Scrub.cbcDecryptChainedReg]

end VG.Artifacts.Sm4Cbc.RISCV64
