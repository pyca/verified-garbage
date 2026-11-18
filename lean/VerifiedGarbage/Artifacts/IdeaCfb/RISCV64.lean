module

public import VerifiedGarbage.Proof.Idea.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Idea.RISCV64.ModesLit
import VerifiedGarbage.Proof.Idea.RISCV64.FbFinalLit

/-! # IDEA-CFB64 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.IdeaCfb.RISCV64

def artifacts : List Artifact := [
  Spec.Idea.cfbEncryptApi.artifact RISCV64.target Proof.Idea.RISCV64.Scrub.cfbEncryptReg,
  Spec.Idea.cfbDecryptApi.artifact RISCV64.target Proof.Idea.RISCV64.Scrub.cfbDecryptReg,
  Spec.Idea.cfbEncryptFinalApi.artifact RISCV64.target Proof.Idea.RISCV64.Scrub.cfbEncryptFinalReg,
  Spec.Idea.cfbDecryptFinalApi.artifact RISCV64.target Proof.Idea.RISCV64.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.IdeaCfb.RISCV64
