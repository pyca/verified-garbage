module

public import VerifiedGarbage.Proof.Aes.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.AesCbc.RISCV64.Lit

/-! # AES-CBC (NIST SP 800-38A §6.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesCbc.RISCV64

def artifacts : List Artifact := [
  Spec.Cbc.aesEncryptApi.artifact RISCV64.target Proof.Aes.RISCV64.Scrub.cbcEncryptReg,
  Spec.Cbc.aesDecryptApi.artifact RISCV64.target Proof.Aes.RISCV64.Scrub.cbcDecryptReg]

end VG.Artifacts.AesCbc.RISCV64
