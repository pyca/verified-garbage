module

public import VerifiedGarbage.Proof.Aes.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.AesCtr.RISCV64.Lit

/-! # AES-CTR (NIST SP 800-38A §6.5) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesCtr.RISCV64

def artifacts : List Artifact := [
  Spec.Ctr.aesApi.artifact RISCV64.target Proof.Aes.RISCV64.Scrub.ctrReg,
  Spec.Ctr.aesFinalApi.artifact RISCV64.target Proof.Aes.RISCV64.Scrub.ctrFinalReg]

end VG.Artifacts.AesCtr.RISCV64
