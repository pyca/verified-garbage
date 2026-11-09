module

public import VerifiedGarbage.Proof.Idea.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Idea.RISCV64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Idea.RISCV64.ModesLit
import VerifiedGarbage.Proof.Idea.RISCV64.FbFinalLit

/-! # IDEA-OFB artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.IdeaOfb.RISCV64

def artifacts : List Artifact := [
  Spec.Idea.ofbApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.ofb
    stack := 64
    verified := Proof.Idea.RISCV64.Modes.ofb_verified },
  Spec.Idea.ofbFinalApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.ofbFinal
    stack := 64
    verified := Proof.Idea.RISCV64.Modes.ofbFinal_verified }]

end VG.Artifacts.IdeaOfb.RISCV64
