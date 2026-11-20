module

public import VerifiedGarbage.Proof.Idea.RISCV64.Scrub
public import VerifiedGarbage.Impl.Idea.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Idea.RISCV64.Lit

/-! # IDEA on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Idea.RISCV64

def artifacts : List Artifact := [
  Spec.Idea.expandKeyApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.Fn.expandKey
    verified := .scrubbed Proof.Idea.RISCV64.Scrub.expandKey_scrubbed },
  Spec.Idea.invertKeyApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.Fn.invertKey
    verified := .scrubbed Proof.Idea.RISCV64.Scrub.invertKey_scrubbed },
  Spec.Idea.ecbApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.Fn.ecb
    verified := .scrubbed Proof.Idea.RISCV64.Scrub.ecb_scrubbed }]

end VG.Artifacts.Idea.RISCV64
