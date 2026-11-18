module

public import VerifiedGarbage.Proof.Seed.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Seed.RISCV64.ModesLit
import VerifiedGarbage.Proof.Seed.RISCV64.FbFinalLit

/-! # SEED-CFB128 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.SeedCfb.RISCV64

def artifacts : List Artifact := [
  Spec.Seed.cfbEncryptApi.artifact RISCV64.target Proof.Seed.RISCV64.Scrub.cfbEncryptReg,
  Spec.Seed.cfbDecryptApi.artifact RISCV64.target Proof.Seed.RISCV64.Scrub.cfbDecryptReg,
  Spec.Seed.cfbEncryptFinalApi.artifact RISCV64.target Proof.Seed.RISCV64.Scrub.cfbEncryptFinalReg,
  Spec.Seed.cfbDecryptFinalApi.artifact RISCV64.target Proof.Seed.RISCV64.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.SeedCfb.RISCV64
