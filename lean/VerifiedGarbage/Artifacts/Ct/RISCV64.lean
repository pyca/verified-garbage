module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ct.Contract
import VerifiedGarbage.Proof.Ct.RISCV64Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Constant-time byte comparison on RISC-V -/

namespace VG.Artifacts.Ct.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Ct.eqApi.artifact RISCV64.target {
    code := Impl.Ct.RISCV64.Fn.eq
    verified := Proof.Ct.RISCV64Scrub.eq_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Ct.RISCV64
