module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Blake2.RISCV64.Verified
public import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blake2.RISCV64.Lit
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Lit

/-! # BLAKE2b (RFC 7693) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Blake2b.RISCV64

def artifacts : List Artifact := [
  Spec.Blake2.initBApi.artifact RISCV64.target {
    code := Impl.Blake2.RISCV64.Stream.init Spec.Blake2.b
    verified := Proof.Blake2.RISCV64.Stream.initB_verified },
  Spec.Blake2.updateBApi.artifact RISCV64.target {
    code := Impl.Blake2.RISCV64.Stream.update Spec.Blake2.b
    stack := 576
    verified := Proof.Blake2.RISCV64.Stream.updateB_verified },
  Spec.Blake2.finalizeBApi.artifact RISCV64.target {
    code := Impl.Blake2.RISCV64.Stream.finalize Spec.Blake2.b
    stack := 576
    verified := Proof.Blake2.RISCV64.Stream.finalizeB_verified }]

end VG.Artifacts.Blake2b.RISCV64
