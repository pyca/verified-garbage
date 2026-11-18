module

public import VerifiedGarbage.Proof.Aes.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # AES-OFB (NIST SP 800-38A §6.4) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesOfb.RISCV64

def artifacts : List Artifact := [
  Spec.Ofb.aesApi.artifact RISCV64.target Proof.Aes.RISCV64.Scrub.ofbReg,
  Spec.Ofb.aesFinalApi.artifact RISCV64.target Proof.Aes.RISCV64.Scrub.ofbFinalReg]

end VG.Artifacts.AesOfb.RISCV64
