module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sha256.RISCV64.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SHA-256 (FIPS 180-4) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sha256.RISCV64

def artifacts : List Artifact := [
  Spec.Sha256.initApi.artifact RISCV64.target {
    code := Impl.Sha256.RISCV64.Stream.init
    verified := Proof.Sha256.RISCV64.Shared.init },
  Spec.Sha256.updateApi.artifact RISCV64.target {
    code := Impl.Sha256.RISCV64.Stream.update
    stack := 144
    verified := Proof.Sha256.RISCV64.Shared.update },
  Spec.Sha256.finalizeApi.artifact RISCV64.target {
    code := Impl.Sha256.RISCV64.Stream.finalize
    stack := 144
    verified := Proof.Sha256.RISCV64.Shared.finalize }]

end VG.Artifacts.Sha256.RISCV64
