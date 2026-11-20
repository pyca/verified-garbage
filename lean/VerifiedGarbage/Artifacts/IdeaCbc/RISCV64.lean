module

public import VerifiedGarbage.Proof.Idea.RISCV64.Scrub
public import VerifiedGarbage.Impl.Idea.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Idea.RISCV64.ModesLit

/-! # IDEA-CBC on RISC-V -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.RISCV64

def artifacts : List Artifact := [
  Spec.Idea.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.Fn.cbcEncryptChained
    verified := .scrubbed Proof.Idea.RISCV64.Scrub.cbcEncryptChained_scrubbed },
  Spec.Idea.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.Fn.cbcDecryptChained
    verified := .scrubbed Proof.Idea.RISCV64.Scrub.cbcDecryptChained_scrubbed }]

end VG.Artifacts.IdeaCbc.RISCV64
