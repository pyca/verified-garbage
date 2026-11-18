module

public import VerifiedGarbage.Proof.Cast5.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Cast5.RISCV64.ModesLit
import VerifiedGarbage.Proof.Cast5.RISCV64.FbFinalLit

/-! # CAST5-CFB64 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Cast5Cfb.RISCV64

def artifacts : List Artifact := [
  Spec.Cast5.cfbEncryptApi.artifact RISCV64.target Proof.Cast5.RISCV64.Scrub.cfbEncryptReg,
  Spec.Cast5.cfbDecryptApi.artifact RISCV64.target Proof.Cast5.RISCV64.Scrub.cfbDecryptReg,
  Spec.Cast5.cfbEncryptFinalApi.artifact RISCV64.target Proof.Cast5.RISCV64.Scrub.cfbEncryptFinalReg,
  Spec.Cast5.cfbDecryptFinalApi.artifact RISCV64.target Proof.Cast5.RISCV64.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.Cast5Cfb.RISCV64
