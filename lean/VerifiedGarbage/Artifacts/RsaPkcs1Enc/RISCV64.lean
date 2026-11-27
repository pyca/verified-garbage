module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Fn
import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Front
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSAES-PKCS1-v1_5 (RFC 8017) on RISC-V -/

namespace VG.Artifacts.RsaPkcs1Enc.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.RsaPkcs1Enc.decryptPrecomputedApi.artifact RISCV64.target {
    code := Impl.RsaPkcs1Enc.RISCV64.Fn.decryptPrecomputed
    verified := Proof.RsaPkcs1Enc.RISCV64.Front.decryptPrecomputed },
  Spec.RsaPkcs1Enc.encryptRandomApi.artifact RISCV64.target {
    code := Impl.RsaPkcs1Enc.RISCV64.Fn.encryptRandom
    verified := Proof.RsaPkcs1Enc.RISCV64.Fn.encryptRandom
    publicOutOk := Proof.RsaPkcs1Enc.RISCV64.Fn.encryptRandom_public }]

spec_apis artifacts

end VG.Artifacts.RsaPkcs1Enc.RISCV64
