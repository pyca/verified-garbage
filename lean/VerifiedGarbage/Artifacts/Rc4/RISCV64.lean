module

public import VerifiedGarbage.Proof.Rc4.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Rc4.RISCV64.Lit

/-! # RC4 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Rc4.RISCV64

def artifacts : List Artifact := [
  Spec.Rc4.initApi.artifact RISCV64.target Proof.Rc4.RISCV64.Scrub.initReg,
  Spec.Rc4.applyApi.artifact RISCV64.target Proof.Rc4.RISCV64.Scrub.applyReg]

end VG.Artifacts.Rc4.RISCV64
