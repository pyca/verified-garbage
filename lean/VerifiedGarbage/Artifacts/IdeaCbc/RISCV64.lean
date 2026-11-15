module

public import VerifiedGarbage.Proof.Idea.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Idea.RISCV64.ModesLit

/-! # IDEA-CBC on RISC-V -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.RISCV64

def artifacts : List Artifact := [
  Spec.Idea.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.cbcEncryptChained
    verified := Proof.Idea.RISCV64.Modes.cbcEncryptChained_verified },
  Spec.Idea.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.cbcDecryptChained
    verified := Proof.Idea.RISCV64.Modes.cbcDecryptChained_verified }]

end VG.Artifacts.IdeaCbc.RISCV64
