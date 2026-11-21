module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # RSASSA-PKCS1-v1_5 (RFC 8017) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Sig.RISCV64

def artifacts : List Artifact := [
  Spec.RsaPkcs1Sig.verifyPrecomputedApi.artifact RISCV64.target {
    code := Impl.RsaPkcs1Sig.RISCV64.Fn.verifyPrecomputed
    verified := Proof.RsaPkcs1Sig.RISCV64.Fn.verifyPrecomputed },
  Spec.RsaPkcs1Sig.recoverPrecomputedApi.artifact RISCV64.target {
    code := Impl.RsaPkcs1Sig.RISCV64.Fn.recoverPrecomputed
    verified := Proof.RsaPkcs1Sig.RISCV64.Fn.recoverPrecomputed },
  Spec.RsaPkcs1Sig.signPrecomputedApi.artifact RISCV64.target {
    code := Impl.RsaPkcs1Sig.RISCV64.Fn.signPrecomputed
    verified := Proof.RsaPkcs1Sig.RISCV64.Fn.signPrecomputed }]

end VG.Artifacts.RsaPkcs1Sig.RISCV64
