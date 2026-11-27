module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Contract
import VerifiedGarbage.Proof.Idea.RISCV64.Scrub
import VerifiedGarbage.Impl.Idea.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA on RISC-V -/

namespace VG.Artifacts.Idea.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Idea.expandKeyApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.Fn.expandKey
    verified := Proof.Idea.RISCV64.Scrub.expandKey_scrubbed },
  Spec.Idea.invertKeyApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.Fn.invertKey
    verified := Proof.Idea.RISCV64.Scrub.invertKey_scrubbed },
  Spec.Idea.ecbApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.Fn.ecb
    verified := Proof.Idea.RISCV64.Scrub.ecb_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Idea.RISCV64
