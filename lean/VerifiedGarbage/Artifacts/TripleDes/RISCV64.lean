module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.TripleDes.RISCV64.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Lit

/-! # Triple DES on RISC-V -/

@[expose] public section

namespace VG.Artifacts.TripleDes.RISCV64

def artifacts : List Artifact := [
  Spec.TripleDes.expandKeyApi.artifact RISCV64.target Proof.TripleDes.RISCV64.Scrub.expandKeyReg,
  Spec.TripleDes.ecbEncryptApi.artifact RISCV64.target Proof.TripleDes.RISCV64.Scrub.ecbEncryptReg,
  Spec.TripleDes.ecbDecryptApi.artifact RISCV64.target Proof.TripleDes.RISCV64.Scrub.ecbDecryptReg]

end VG.Artifacts.TripleDes.RISCV64
