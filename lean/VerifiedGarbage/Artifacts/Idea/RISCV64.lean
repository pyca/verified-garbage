module

public import VerifiedGarbage.Proof.Idea.RISCV64.Invert
public import VerifiedGarbage.Proof.Idea.RISCV64.Key
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.RISCV64.Lit

/-! # IDEA artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.Idea.RISCV64

def artifacts : List Artifact := [
  Spec.Idea.expandKeyApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.expandKey
    verified := Proof.Idea.RISCV64.expandKey_verified },
  Spec.Idea.invertKeyApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.invertKey
    verified := Proof.Idea.RISCV64.invertKey_verified },
  Spec.Idea.ecbApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.ecb
    verified := Proof.Idea.RISCV64.ecb_verified }]

end VG.Artifacts.Idea.RISCV64
