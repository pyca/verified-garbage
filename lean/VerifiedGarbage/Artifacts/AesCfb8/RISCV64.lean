module

public import VerifiedGarbage.Proof.Aes.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.AesCfb8.RISCV64.Lit

/-! # AES-CFB8 (NIST SP 800-38A §6.3) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesCfb8.RISCV64

def artifacts : List Artifact := [
  Spec.Cfb8.aesEncryptApi.artifact RISCV64.target Proof.Aes.RISCV64.Scrub.cfb8EncryptReg,
  Spec.Cfb8.aesDecryptApi.artifact RISCV64.target Proof.Aes.RISCV64.Scrub.cfb8DecryptReg]

end VG.Artifacts.AesCfb8.RISCV64
