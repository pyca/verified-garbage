module

public import VerifiedGarbage.Proof.Idea.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.RISCV64.ModesLit

/-! # IDEA-CBC artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.RISCV64

def artifacts : List Artifact := [
  Spec.Idea.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.cbcEncryptChained
    stack := 64
    verified := Proof.Idea.RISCV64.Modes.cbcEncryptChained_verified },
  Spec.Idea.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.cbcDecryptChained
    stack := 64
    verified := Proof.Idea.RISCV64.Modes.cbcDecryptChained_verified }]

end VG.Artifacts.IdeaCbc.RISCV64
