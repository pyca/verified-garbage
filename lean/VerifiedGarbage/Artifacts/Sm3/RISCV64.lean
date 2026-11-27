module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm3.Contract
import VerifiedGarbage.Proof.Sm3.RISCV64.Scrub
import VerifiedGarbage.Impl.Sm3.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM3 (GB/T 32905-2016) on RISC-V -/

namespace VG.Artifacts.Sm3.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Sm3.initApi.artifact RISCV64.target {
    code := Impl.Sm3.RISCV64.Fn.init
    verified := Proof.Sm3.RISCV64.init_scrubbed },
  Spec.Sm3.updateApi.artifact RISCV64.target {
    code := Impl.Sm3.RISCV64.Fn.update
    verified := Proof.Sm3.RISCV64.update_scrubbed },
  Spec.Sm3.finalizeApi.artifact RISCV64.target {
    code := Impl.Sm3.RISCV64.Fn.finalize
    verified := Proof.Sm3.RISCV64.finalize_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sm3.RISCV64
