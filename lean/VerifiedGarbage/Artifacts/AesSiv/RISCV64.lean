module

public import VerifiedGarbage.Proof.AesSiv.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # AES-SIV (RFC 5297) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesSiv.RISCV64

def artifacts : List Artifact := [
  Spec.Siv.initApi.artifact RISCV64.target Proof.AesSiv.RISCV64.Scrub.initReg,
  Spec.Siv.encryptApi.artifact RISCV64.target Proof.AesSiv.RISCV64.Scrub.encryptReg,
  Spec.Siv.decryptApi.artifact RISCV64.target Proof.AesSiv.RISCV64.Scrub.decryptReg]

end VG.Artifacts.AesSiv.RISCV64
