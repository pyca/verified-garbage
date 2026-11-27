module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Rc2.Contract
import VerifiedGarbage.Proof.Rc2.RISCV64.Scrub
import VerifiedGarbage.Impl.Rc2.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Rc2.RISCV64.Lit
import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Lit
import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RC2 on RISC-V -/

namespace VG.Artifacts.Rc2.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Rc2.cbcInitApi.artifact RISCV64.target {
    code := Impl.Rc2.RISCV64.Fn.cbcInit
    verified := Proof.Rc2.RISCV64.Scrub.cbcInit_scrubbed },
  Spec.Rc2.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.Rc2.RISCV64.Fn.cbcEncryptChained
    verified := Proof.Rc2.RISCV64.Scrub.cbcEncryptChained_scrubbed },
  Spec.Rc2.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.Rc2.RISCV64.Fn.cbcDecryptChained
    verified := Proof.Rc2.RISCV64.Scrub.cbcDecryptChained_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Rc2.RISCV64
