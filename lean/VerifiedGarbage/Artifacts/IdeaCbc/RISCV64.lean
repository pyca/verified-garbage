module

public import VerifiedGarbage.Proof.Idea.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Idea.RISCV64.ModesLit

/-! # IDEA-CBC on RISC-V -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.RISCV64

def artifacts : List Artifact := [
  Spec.Idea.cbcEncryptChainedApi.artifact RISCV64.target Proof.Idea.RISCV64.Scrub.cbcEncryptChainedReg,
  Spec.Idea.cbcDecryptChainedApi.artifact RISCV64.target Proof.Idea.RISCV64.Scrub.cbcDecryptChainedReg]

end VG.Artifacts.IdeaCbc.RISCV64
