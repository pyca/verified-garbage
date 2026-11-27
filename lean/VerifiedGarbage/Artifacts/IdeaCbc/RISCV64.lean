module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Cbc
import VerifiedGarbage.Proof.Idea.RISCV64.Scrub
import VerifiedGarbage.Impl.Idea.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.RISCV64.ModesLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA-CBC on RISC-V -/

namespace VG.Artifacts.IdeaCbc.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Idea.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.Fn.cbcEncryptChained
    verified := Proof.Idea.RISCV64.Scrub.cbcEncryptChained_scrubbed },
  Spec.Idea.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.Fn.cbcDecryptChained
    verified := Proof.Idea.RISCV64.Scrub.cbcDecryptChained_scrubbed }]

spec_apis artifacts

end VG.Artifacts.IdeaCbc.RISCV64
