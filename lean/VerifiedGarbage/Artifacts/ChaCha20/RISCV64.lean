module

public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Scrub
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # ChaCha20 (RFC 8439) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.ChaCha20.RISCV64

def artifacts : List Artifact := [
  Spec.ChaCha20.initApi.artifact RISCV64.target Proof.ChaCha20.RISCV64.Scrub.initReg,
  Spec.ChaCha20.setNonceApi.artifact RISCV64.target Proof.ChaCha20.RISCV64.Scrub.setNonceReg,
  Spec.ChaCha20.applyApi.artifact RISCV64.target Proof.ChaCha20.RISCV64.Scrub.applyReg]

end VG.Artifacts.ChaCha20.RISCV64
