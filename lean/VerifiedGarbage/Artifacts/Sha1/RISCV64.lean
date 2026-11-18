module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sha1.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # SHA-1 (FIPS 180-4) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sha1.RISCV64

def artifacts : List Artifact := [
  Spec.Sha1.initApi.artifact RISCV64.target Proof.Sha1.RISCV64.initReg,
  Spec.Sha1.updateApi.artifact RISCV64.target Proof.Sha1.RISCV64.updateReg,
  Spec.Sha1.finalizeApi.artifact RISCV64.target Proof.Sha1.RISCV64.finalizeReg,
  Spec.Sha1.digestApi.artifact RISCV64.target Proof.Sha1.RISCV64.digestReg]

end VG.Artifacts.Sha1.RISCV64
