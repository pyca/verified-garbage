module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Ed448 (RFC 8032) on RISC-V -/

namespace VG.Artifacts.Ed448.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Ed448.publicKeyApi.artifact RISCV64.target {
    code := Impl.Ed448.RISCV64.Fn.publicKey
    verified := Proof.Ed448.RISCV64.Fn.publicKey },
  Spec.Ed448.signCachedApi.artifact RISCV64.target {
    code := Impl.Ed448.RISCV64.Fn.signCached
    verified := Proof.Ed448.RISCV64.Fn.signCached },
  Spec.Ed448.verifyApi.artifact RISCV64.target {
    code := Impl.Ed448.RISCV64.Fn.verify
    verified := Proof.Ed448.RISCV64.Fn.verify }]

spec_apis artifacts

end VG.Artifacts.Ed448.RISCV64
