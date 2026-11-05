module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.EncVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # RSAES-PKCS1-v1_5 (RFC 8017) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Enc.RISCV64

def artifacts : List Artifact := [
  Spec.RsaPkcs1Enc.encryptPrecomputedApi.artifact RISCV64.target {
    code := Impl.RsaPkcs1Enc.RISCV64.Precomputed.code
    stack := 2128
    verified := Proof.RsaPkcs1Enc.RISCV64.Enc.code_verified },
  Spec.RsaPkcs1Enc.decryptApi.artifact RISCV64.target {
    code := Impl.RsaPkcs1Enc.RISCV64.Decrypt.code
    stack := Proof.RsaPkcs1Enc.RISCV64.Dec.stackBytes
    verified := Proof.RsaPkcs1Enc.RISCV64.Dec.dec_verified }]

end VG.Artifacts.RsaPkcs1Enc.RISCV64
