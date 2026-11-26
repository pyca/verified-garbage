module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Ctr
public import VerifiedGarbage.Spec.Camellia.CtrFinal
import VerifiedGarbage.Proof.Camellia.RISCV64.Scrub
import VerifiedGarbage.Impl.Camellia.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia-CTR on RISC-V -/

namespace VG.Artifacts.CamelliaCtr.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Camellia.ctrApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.ctr
    verified := Proof.Camellia.RISCV64.Scrub.ctr_scrubbed },
  Spec.Camellia.ctrFinalApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.ctrFinal
    verified := Proof.Camellia.RISCV64.Scrub.ctrFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.CamelliaCtr.RISCV64
