module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Ofb
public import VerifiedGarbage.Spec.Idea.OfbFinal
import VerifiedGarbage.Proof.Idea.RISCV64.Scrub
import VerifiedGarbage.Impl.Idea.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.RISCV64.ModesLit
import VerifiedGarbage.Proof.Idea.RISCV64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA-OFB on RISC-V -/

namespace VG.Artifacts.IdeaOfb.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Idea.ofbApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.Fn.ofb
    verified := Proof.Idea.RISCV64.Scrub.ofb_scrubbed },
  Spec.Idea.ofbFinalApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.Fn.ofbFinal
    verified := Proof.Idea.RISCV64.Scrub.ofbFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.IdeaOfb.RISCV64
