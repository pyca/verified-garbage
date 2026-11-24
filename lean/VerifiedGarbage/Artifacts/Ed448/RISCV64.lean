module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed448.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed448 (RFC 8032) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ed448.RISCV64

def artifacts : List (Artifact RISCV64.target) := [
  Spec.Ed448.publicKeyApi.artifact RISCV64.target {
    code := Impl.Ed448.RISCV64.Fn.publicKey
    verified := Proof.Ed448.RISCV64.Fn.publicKey },
  Spec.Ed448.signCachedApi.artifact RISCV64.target {
    code := Impl.Ed448.RISCV64.Fn.signCached
    verified := Proof.Ed448.RISCV64.Fn.signCached },
  Spec.Ed448.verifyApi.artifact RISCV64.target {
    code := Impl.Ed448.RISCV64.Fn.verify
    verified := Proof.Ed448.RISCV64.Fn.verify }]

end VG.Artifacts.Ed448.RISCV64
