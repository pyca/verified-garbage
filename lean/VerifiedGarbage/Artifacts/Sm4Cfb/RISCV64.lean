module

public import VerifiedGarbage.Proof.Sm4.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
import VerifiedGarbage.Proof.Sm4.RISCV64.FbFinalLit

/-! # SM4-CFB128 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.RISCV64

def artifacts : List Artifact := [
  Spec.Sm4.cfbEncryptApi.artifact RISCV64.target Proof.Sm4.RISCV64.Scrub.cfbEncryptReg,
  Spec.Sm4.cfbDecryptApi.artifact RISCV64.target Proof.Sm4.RISCV64.Scrub.cfbDecryptReg,
  Spec.Sm4.cfbEncryptFinalApi.artifact RISCV64.target Proof.Sm4.RISCV64.Scrub.cfbEncryptFinalReg,
  Spec.Sm4.cfbDecryptFinalApi.artifact RISCV64.target Proof.Sm4.RISCV64.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.Sm4Cfb.RISCV64
