module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Rc4.Contract
import VerifiedGarbage.Proof.Rc4.RISCV64.Scrub
import VerifiedGarbage.Impl.Rc4.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Rc4.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RC4 on RISC-V -/

namespace VG.Artifacts.Rc4.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Rc4.initApi.artifact RISCV64.target {
    code := Impl.Rc4.RISCV64.Fn.init
    verified := Proof.Rc4.RISCV64.Scrub.init_scrubbed },
  Spec.Rc4.applyApi.artifact RISCV64.target {
    code := Impl.Rc4.RISCV64.Fn.apply
    verified := Proof.Rc4.RISCV64.Scrub.apply_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Rc4.RISCV64
