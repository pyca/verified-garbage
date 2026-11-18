module

public import VerifiedGarbage.Proof.Idea.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Idea.RISCV64.Lit

/-! # IDEA on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Idea.RISCV64

def artifacts : List Artifact := [
  Spec.Idea.expandKeyApi.artifact RISCV64.target Proof.Idea.RISCV64.Scrub.expandKeyReg,
  Spec.Idea.invertKeyApi.artifact RISCV64.target Proof.Idea.RISCV64.Scrub.invertKeyReg,
  Spec.Idea.ecbApi.artifact RISCV64.target Proof.Idea.RISCV64.Scrub.ecbReg]

end VG.Artifacts.Idea.RISCV64
