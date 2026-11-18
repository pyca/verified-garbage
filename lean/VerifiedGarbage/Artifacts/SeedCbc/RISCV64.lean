module

public import VerifiedGarbage.Proof.Seed.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Seed.RISCV64.ModesLit

/-! # SEED-CBC on RISC-V -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.RISCV64

def artifacts : List Artifact := [
  Spec.Seed.cbcEncryptChainedApi.artifact RISCV64.target Proof.Seed.RISCV64.Scrub.cbcEncryptChainedReg,
  Spec.Seed.cbcDecryptChainedApi.artifact RISCV64.target Proof.Seed.RISCV64.Scrub.cbcDecryptChainedReg]

end VG.Artifacts.SeedCbc.RISCV64
