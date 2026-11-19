module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.VerifyVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.RecoverVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Sign.Verified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.SignPrecomputed
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rsa.RISCV64.Scrub
public import VerifiedGarbage.TCB.RISCV64.Print
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved

/-! # RSASSA-PKCS1-v1_5 (RFC 8017) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Sig.RISCV64

def artifacts : List Artifact := [
  Spec.RsaPkcs1Sig.verifyPrecomputedApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.RsaPkcs1Sig.RISCV64.Precomputed.code
    verified := Proof.RsaPkcs1Sig.RISCV64.Ver.code_verified }
    (Proof.Rsa.RISCV64.Scrub.pkcs1VerifyOut _)),
  Spec.RsaPkcs1Sig.recoverPrecomputedApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.RsaPkcs1Sig.RISCV64.RecoverPrecomputed.code
    verified := Proof.RsaPkcs1Sig.RISCV64.Rec.code_verified }
    (Proof.Rsa.RISCV64.Scrub.pkcs1RecoverOut _)),
  Spec.RsaPkcs1Sig.signPrecomputedApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.RsaPkcs1Sig.RISCV64.Sign.codeP
    verified := Proof.RsaPkcs1Sig.RISCV64.Sign.codeP_verified }
    (Proof.Rsa.RISCV64.Scrub.pkcs1SignOut _))]

end VG.Artifacts.RsaPkcs1Sig.RISCV64
