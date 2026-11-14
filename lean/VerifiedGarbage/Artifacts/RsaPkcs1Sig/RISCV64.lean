module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.VerifyVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.RecoverVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Sign.Verified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.SignPrecomputed
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # RSASSA-PKCS1-v1_5 (RFC 8017) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Sig.RISCV64

def artifacts : List Artifact := [
  Spec.RsaPkcs1Sig.verifyPrecomputedApi.artifact RISCV64.target {
    code := Impl.RsaPkcs1Sig.RISCV64.Precomputed.code
    stack := 2128
    verified := Proof.RsaPkcs1Sig.RISCV64.Ver.code_verified },
  Spec.RsaPkcs1Sig.recoverPrecomputedApi.artifact RISCV64.target {
    code := Impl.RsaPkcs1Sig.RISCV64.RecoverPrecomputed.code
    stack := 2128
    verified := Proof.RsaPkcs1Sig.RISCV64.Rec.code_verified },
  Spec.RsaPkcs1Sig.signPrecomputedApi.artifact RISCV64.target {
    code := Impl.RsaPkcs1Sig.RISCV64.Sign.codeP
    stack := Proof.RsaPkcs1Sig.RISCV64.Sign.stackBytes
    verified := Proof.RsaPkcs1Sig.RISCV64.Sign.codeP_verified }]

end VG.Artifacts.RsaPkcs1Sig.RISCV64
