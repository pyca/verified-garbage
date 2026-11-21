module

public import VerifiedGarbage.Proof.Idea.RISCV64.Scrub
public import VerifiedGarbage.Impl.Idea.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Idea.RISCV64.ModesLit
import VerifiedGarbage.Proof.Idea.RISCV64.FbFinalLit

/-! # IDEA-OFB on RISC-V -/

@[expose] public section

namespace VG.Artifacts.IdeaOfb.RISCV64

def artifacts : List Artifact := [
  Spec.Idea.ofbApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.Fn.ofb
    verified := Proof.Idea.RISCV64.Scrub.ofb_scrubbed },
  Spec.Idea.ofbFinalApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.Fn.ofbFinal
    verified := Proof.Idea.RISCV64.Scrub.ofbFinal_scrubbed }]

end VG.Artifacts.IdeaOfb.RISCV64
