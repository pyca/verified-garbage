module

public import VerifiedGarbage.Proof.Aes.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit

/-! # AES (FIPS 197) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Aes.RISCV64

def artifacts : List Artifact := [
  Spec.Aes.expandKeyApi.artifact RISCV64.target Proof.Aes.RISCV64.Scrub.expandKeyReg]

end VG.Artifacts.Aes.RISCV64
