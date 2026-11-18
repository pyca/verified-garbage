module

public import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # AES-CMAC (NIST SP 800-38B) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.CmacAes.RISCV64

def artifacts : List Artifact := [
  Spec.Cmac.aesInitApi.artifact RISCV64.target Proof.CmacAes.Stream.RISCV64.Scrub.initReg,
  Spec.Cmac.aesAbsorbApi.artifact RISCV64.target Proof.CmacAes.Stream.RISCV64.Scrub.absorbReg,
  Spec.Cmac.aesFinishApi.artifact RISCV64.target Proof.CmacAes.Stream.RISCV64.Scrub.finishReg]

end VG.Artifacts.CmacAes.RISCV64
