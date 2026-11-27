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

/-! # BLAKE2s (RFC 7693) on RISC-V -/

namespace VG.Artifacts.Blake2s.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Blake2.initSApi.artifact RISCV64.target {
    code := Impl.Blake2.RISCV64.Fn.initS
    verified := Proof.Blake2.RISCV64.initS_scrubbed },
  Spec.Blake2.updateSApi.artifact RISCV64.target {
    code := Impl.Blake2.RISCV64.Fn.updateS
    verified := Proof.Blake2.RISCV64.updateS_scrubbed },
  Spec.Blake2.finalizeSApi.artifact RISCV64.target {
    code := Impl.Blake2.RISCV64.Fn.finalizeS
    verified := Proof.Blake2.RISCV64.finalizeS_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Blake2s.RISCV64
