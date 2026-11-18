module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Blowfish.RISCV64.Lit

/-! # Blowfish on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Blowfish.RISCV64

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact RISCV64.target Proof.Blowfish.RISCV64.Scrub.expandKeyReg,
  Spec.Blowfish.ecbEncryptApi.artifact RISCV64.target Proof.Blowfish.RISCV64.Scrub.ecbEncryptReg,
  Spec.Blowfish.ecbDecryptApi.artifact RISCV64.target Proof.Blowfish.RISCV64.Scrub.ecbDecryptReg]

end VG.Artifacts.Blowfish.RISCV64
