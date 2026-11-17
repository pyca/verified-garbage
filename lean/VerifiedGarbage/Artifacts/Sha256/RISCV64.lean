module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sha256.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # SHA-256 (FIPS 180-4) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sha256.RISCV64

def artifacts : List Artifact := [
  Spec.Sha256.init224Api.artifact RISCV64.target Proof.Sha256.RISCV64.init224Reg,
  Spec.Sha256.finalize224Api.artifact RISCV64.target Proof.Sha256.RISCV64.finalize224Reg,
  Spec.Sha256.digest224Api.artifact RISCV64.target Proof.Sha256.RISCV64.digest224Reg,
  Spec.Sha256.initApi.artifact RISCV64.target Proof.Sha256.RISCV64.initReg,
  Spec.Sha256.updateApi.artifact RISCV64.target Proof.Sha256.RISCV64.updateReg,
  Spec.Sha256.finalizeApi.artifact RISCV64.target Proof.Sha256.RISCV64.finalizeReg,
  Spec.Sha256.digest256Api.artifact RISCV64.target Proof.Sha256.RISCV64.digest256Reg]

end VG.Artifacts.Sha256.RISCV64
