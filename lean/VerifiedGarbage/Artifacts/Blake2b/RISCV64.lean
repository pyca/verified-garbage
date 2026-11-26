module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.Proof.Blake2.RISCV64.Scrub
import VerifiedGarbage.Impl.Blake2.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blake2.RISCV64.Lit
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # BLAKE2b (RFC 7693) on RISC-V -/

namespace VG.Artifacts.Blake2b.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Blake2.initBApi.artifact RISCV64.target {
    code := Impl.Blake2.RISCV64.Fn.initB
    verified := Proof.Blake2.RISCV64.initB_scrubbed },
  Spec.Blake2.updateBApi.artifact RISCV64.target {
    code := Impl.Blake2.RISCV64.Fn.updateB
    verified := Proof.Blake2.RISCV64.updateB_scrubbed },
  Spec.Blake2.finalizeBApi.artifact RISCV64.target {
    code := Impl.Blake2.RISCV64.Fn.finalizeB
    verified := Proof.Blake2.RISCV64.finalizeB_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Blake2b.RISCV64
