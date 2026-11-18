module

public import VerifiedGarbage.Proof.Aes.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesCfb.RISCV64

def artifacts : List Artifact := [
  Spec.Cfb.aesEncryptApi.artifact RISCV64.target Proof.Aes.RISCV64.Scrub.cfbEncryptReg,
  Spec.Cfb.aesDecryptApi.artifact RISCV64.target Proof.Aes.RISCV64.Scrub.cfbDecryptReg,
  Spec.Cfb.aesEncryptFinalApi.artifact RISCV64.target Proof.Aes.RISCV64.Scrub.cfbEncryptFinalReg,
  Spec.Cfb.aesDecryptFinalApi.artifact RISCV64.target Proof.Aes.RISCV64.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.AesCfb.RISCV64
