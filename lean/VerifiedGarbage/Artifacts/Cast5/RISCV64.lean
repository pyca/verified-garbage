module

public import VerifiedGarbage.Proof.Cast5.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Cast5.RISCV64.Lit

/-! # CAST5 (RFC 2144) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Cast5.RISCV64

def artifacts : List Artifact := [
  Spec.Cast5.expandKeyApi.artifact RISCV64.target Proof.Cast5.RISCV64.Scrub.expandKeyReg,
  Spec.Cast5.ecbEncryptApi.artifact RISCV64.target Proof.Cast5.RISCV64.Scrub.ecbEncryptReg,
  Spec.Cast5.ecbDecryptApi.artifact RISCV64.target Proof.Cast5.RISCV64.Scrub.ecbDecryptReg]

end VG.Artifacts.Cast5.RISCV64
