module

public import VerifiedGarbage.Proof.Ct.RISCV64Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Target

/-! # Constant-time byte comparison on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ct.RISCV64

def artifacts : List (Artifact RISCV64.target) := [
  Spec.Ct.eqApi.artifact RISCV64.target {
    code := Impl.Ct.RISCV64.Fn.eq
    verified := Proof.Ct.RISCV64Scrub.eq_scrubbed }]

end VG.Artifacts.Ct.RISCV64
