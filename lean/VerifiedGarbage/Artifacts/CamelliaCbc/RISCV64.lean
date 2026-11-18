module

public import VerifiedGarbage.Proof.Camellia.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit

/-! # Camellia-CBC on RISC-V -/

@[expose] public section

namespace VG.Artifacts.CamelliaCbc.RISCV64

def artifacts : List Artifact := [
  Spec.Camellia.cbcEncryptChainedApi.artifact RISCV64.target Proof.Camellia.RISCV64.Scrub.cbcEncryptChainedReg,
  Spec.Camellia.cbcDecryptChainedApi.artifact RISCV64.target Proof.Camellia.RISCV64.Scrub.cbcDecryptChainedReg]

end VG.Artifacts.CamelliaCbc.RISCV64
