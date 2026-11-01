module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sm3.RISCV64.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SM3 (GB/T 32905-2016) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm3.RISCV64

def artifacts : List Artifact := [
  Spec.Sm3.initApi.artifact RISCV64.target {
    code := Impl.Sm3.RISCV64.Stream.init
    verified := Proof.Sm3.RISCV64.Shared.init },
  Spec.Sm3.updateApi.artifact RISCV64.target {
    code := Impl.Sm3.RISCV64.Stream.update
    stack := 144
    verified := Proof.Sm3.RISCV64.Shared.update },
  Spec.Sm3.finalizeApi.artifact RISCV64.target {
    code := Impl.Sm3.RISCV64.Stream.finalize
    stack := 144
    verified := Proof.Sm3.RISCV64.Shared.finalize }]

end VG.Artifacts.Sm3.RISCV64
