module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.Spec.Sm4.CtrFinal
import VerifiedGarbage.Proof.Sm4.RISCV64.Scrub
import VerifiedGarbage.Impl.Sm4.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-CTR on RISC-V -/

namespace VG.Artifacts.Sm4Ctr.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Sm4.ctrApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.ctr
    verified := Proof.Sm4.RISCV64.Scrub.ctr_scrubbed },
  Spec.Sm4.ctrFinalApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.ctrFinal
    verified := Proof.Sm4.RISCV64.Scrub.ctrFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sm4Ctr.RISCV64
