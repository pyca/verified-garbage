module

public import VerifiedGarbage.Proof.Seed.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Seed.RISCV64.Lit

/-! # SEED on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Seed.RISCV64

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact RISCV64.target Proof.Seed.RISCV64.Scrub.expandKeyReg,
  Spec.Seed.ecbEncryptApi.artifact RISCV64.target Proof.Seed.RISCV64.Scrub.ecbEncryptReg,
  Spec.Seed.ecbDecryptApi.artifact RISCV64.target Proof.Seed.RISCV64.Scrub.ecbDecryptReg]

end VG.Artifacts.Seed.RISCV64
