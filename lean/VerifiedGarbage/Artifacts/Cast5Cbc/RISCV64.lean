module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cast5.Cbc
import VerifiedGarbage.Proof.Cast5.RISCV64.Scrub
import VerifiedGarbage.Impl.Cast5.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Cast5.RISCV64.ModesLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # CAST5-CBC on RISC-V -/

namespace VG.Artifacts.Cast5Cbc.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Cast5.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.Fn.cbcEncryptChained
    verified := Proof.Cast5.RISCV64.Scrub.cbcEncryptChained_scrubbed },
  Spec.Cast5.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.Fn.cbcDecryptChained
    verified := Proof.Cast5.RISCV64.Scrub.cbcDecryptChained_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Cast5Cbc.RISCV64
