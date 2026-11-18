module

public import VerifiedGarbage.Proof.Sm4.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Sm4.RISCV64.Lit

/-! # SM4 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm4.RISCV64

def artifacts : List Artifact := [
  Spec.Sm4.expandKeyApi.artifact RISCV64.target Proof.Sm4.RISCV64.Scrub.expandKeyReg,
  Spec.Sm4.ecbEncryptApi.artifact RISCV64.target Proof.Sm4.RISCV64.Scrub.ecbEncryptReg,
  Spec.Sm4.ecbDecryptApi.artifact RISCV64.target Proof.Sm4.RISCV64.Scrub.ecbDecryptReg]

end VG.Artifacts.Sm4.RISCV64
