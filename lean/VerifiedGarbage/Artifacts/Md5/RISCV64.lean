module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Md5.RISCV64.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-! # MD5 (RFC 1321) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Md5.RISCV64

def artifacts : List Artifact := [
  Spec.Md5.initApi.artifact RISCV64.target {
    code := Impl.Md5.RISCV64.Stream.init
    verified := Proof.Md5.RISCV64.Shared.init },
  Spec.Md5.updateApi.artifact RISCV64.target {
    code := Impl.Md5.RISCV64.Stream.update
    stack := 144
    verified := Proof.Md5.RISCV64.Shared.update },
  Spec.Md5.finalizeApi.artifact RISCV64.target {
    code := Impl.Md5.RISCV64.Stream.finalize
    stack := 144
    verified := Proof.Md5.RISCV64.Shared.finalize }]

end VG.Artifacts.Md5.RISCV64
