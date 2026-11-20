module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Blake2.RISCV64.Scrub
public import VerifiedGarbage.Impl.Blake2.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Blake2.RISCV64.Lit
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Lit

/-! # BLAKE2b (RFC 7693) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Blake2b.RISCV64

def artifacts : List Artifact := [
  Spec.Blake2.initBApi.artifact RISCV64.target {
    code := Impl.Blake2.RISCV64.Fn.initB
    verified := .scrubbed Proof.Blake2.RISCV64.initB_scrubbed },
  Spec.Blake2.updateBApi.artifact RISCV64.target {
    code := Impl.Blake2.RISCV64.Fn.updateB
    verified := .scrubbed Proof.Blake2.RISCV64.updateB_scrubbed },
  Spec.Blake2.finalizeBApi.artifact RISCV64.target {
    code := Impl.Blake2.RISCV64.Fn.finalizeB
    verified := .scrubbed Proof.Blake2.RISCV64.finalizeB_scrubbed }]

end VG.Artifacts.Blake2b.RISCV64
