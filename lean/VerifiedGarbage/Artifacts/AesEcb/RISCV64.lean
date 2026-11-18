module

public import VerifiedGarbage.Proof.Aes.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit

/-! # AES-ECB (NIST SP 800-38A §6.1) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesEcb.RISCV64

def artifacts : List Artifact := [
  Spec.AesEcb.encryptApi.artifact RISCV64.target Proof.Aes.RISCV64.Scrub.ecbEncryptReg,
  Spec.AesEcb.decryptApi.artifact RISCV64.target Proof.Aes.RISCV64.Scrub.ecbDecryptReg]

end VG.Artifacts.AesEcb.RISCV64
