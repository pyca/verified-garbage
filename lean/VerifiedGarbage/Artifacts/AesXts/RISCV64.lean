module

public import VerifiedGarbage.Proof.AesXts.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.AesXts.RISCV64.Lit

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesXts.RISCV64

def artifacts : List Artifact := [
  Spec.Xts.aesEncryptUnitApi.artifact RISCV64.target Proof.AesXts.RISCV64.Scrub.encryptUnitReg,
  Spec.Xts.aesDecryptUnitApi.artifact RISCV64.target Proof.AesXts.RISCV64.Scrub.decryptUnitReg]

end VG.Artifacts.AesXts.RISCV64
