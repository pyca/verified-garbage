module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Md5.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # MD5 (RFC 1321) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Md5.RISCV64

def artifacts : List Artifact := [
  Spec.Md5.initApi.artifact RISCV64.target Proof.Md5.RISCV64.initReg,
  Spec.Md5.updateApi.artifact RISCV64.target Proof.Md5.RISCV64.updateReg,
  Spec.Md5.finalizeApi.artifact RISCV64.target Proof.Md5.RISCV64.finalizeReg]

end VG.Artifacts.Md5.RISCV64
