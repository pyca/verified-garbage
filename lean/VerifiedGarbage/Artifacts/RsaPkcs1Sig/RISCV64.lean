module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSASSA-PKCS1-v1_5 (RFC 8017) on RISC-V -/

namespace VG.Artifacts.RsaPkcs1Sig.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.RsaPkcs1Sig.verifyPrecomputedApi.artifact RISCV64.target {
    code := Impl.RsaPkcs1Sig.RISCV64.Fn.verifyPrecomputed
    verified := Proof.RsaPkcs1Sig.RISCV64.Fn.verifyPrecomputed },
  Spec.RsaPkcs1Sig.recoverPrecomputedApi.artifact RISCV64.target {
    code := Impl.RsaPkcs1Sig.RISCV64.Fn.recoverPrecomputed
    verified := Proof.RsaPkcs1Sig.RISCV64.Fn.recoverPrecomputed },
  Spec.RsaPkcs1Sig.signPrecomputedApi.artifact RISCV64.target {
    code := Impl.RsaPkcs1Sig.RISCV64.Fn.signPrecomputed
    verified := Proof.RsaPkcs1Sig.RISCV64.Fn.signPrecomputed }]

spec_apis artifacts

end VG.Artifacts.RsaPkcs1Sig.RISCV64
