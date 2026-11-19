module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.CmacTripleDes.RISCV64

def artifacts : List Artifact := [
  Spec.Cmac.tdesStreamInitApi.artifact RISCV64.target Proof.CmacTripleDes.Stream.RISCV64.Scrub.initReg,
  Spec.Cmac.tdesAbsorbApi.artifact RISCV64.target Proof.CmacTripleDes.Stream.RISCV64.Scrub.absorbReg,
  Spec.Cmac.tdesFinishApi.artifact RISCV64.target Proof.CmacTripleDes.Stream.RISCV64.Scrub.finishReg]

end VG.Artifacts.CmacTripleDes.RISCV64
