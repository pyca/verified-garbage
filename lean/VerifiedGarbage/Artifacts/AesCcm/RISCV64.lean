module

public import VerifiedGarbage.Proof.AesCcm.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # AES-CCM (NIST SP 800-38C) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesCcm.RISCV64

def artifacts : List Artifact := [
  Spec.Ccm.sealApi.artifact RISCV64.target Proof.AesCcm.RISCV64.Scrub.sealReg,
  Spec.Ccm.openApi.artifact RISCV64.target Proof.AesCcm.RISCV64.Scrub.openReg]

end VG.Artifacts.AesCcm.RISCV64
