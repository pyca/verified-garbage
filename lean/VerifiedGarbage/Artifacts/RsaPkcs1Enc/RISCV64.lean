module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # RSAES-PKCS1-v1_5 (RFC 8017) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Enc.RISCV64

def artifacts : List Artifact := [
  Spec.RsaPkcs1Enc.decryptPrecomputedApi.artifact RISCV64.target {
    code := Impl.RsaPkcs1Enc.RISCV64.Fn.decryptPrecomputed
    verified := .scrubbed Proof.RsaPkcs1Enc.RISCV64.Fn.decryptPrecomputed },
  Spec.RsaPkcs1Enc.encryptRandomApi.artifact RISCV64.target {
    code := Impl.RsaPkcs1Enc.RISCV64.Fn.encryptRandom
    verified := .scrubbed Proof.RsaPkcs1Enc.RISCV64.Fn.encryptRandom }]

end VG.Artifacts.RsaPkcs1Enc.RISCV64
