module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Blake2.RISCV64.Verified
public import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blake2.RISCV64.Lit
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Lit

/-! # BLAKE2s (RFC 7693) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Blake2s.RISCV64

def artifacts : List Artifact := [
  Spec.Blake2.initSApi.artifact RISCV64.target {
    code := Impl.Blake2.RISCV64.Stream.init Spec.Blake2.s
    verified := Proof.Blake2.RISCV64.Stream.initS_verified },
  Spec.Blake2.updateSApi.artifact RISCV64.target {
    code := Impl.Blake2.RISCV64.Stream.update Spec.Blake2.s
    stack := 576
    verified := Proof.Blake2.RISCV64.Stream.updateS_verified },
  Spec.Blake2.finalizeSApi.artifact RISCV64.target {
    code := Impl.Blake2.RISCV64.Stream.finalize Spec.Blake2.s
    stack := 576
    verified := Proof.Blake2.RISCV64.Stream.finalizeS_verified }]

end VG.Artifacts.Blake2s.RISCV64
