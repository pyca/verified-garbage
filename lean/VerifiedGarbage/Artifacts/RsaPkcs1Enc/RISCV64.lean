module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.EncVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Verified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.DecPrecomputed
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.RndVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rsa.RISCV64.Scrub
public import VerifiedGarbage.TCB.RISCV64.Print
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved

/-! # RSAES-PKCS1-v1_5 (RFC 8017) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Enc.RISCV64

def artifacts : List Artifact := [
  Spec.RsaPkcs1Enc.decryptPrecomputedApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.RsaPkcs1Enc.RISCV64.Decrypt.codeP
    verified := Proof.RsaPkcs1Enc.RISCV64.Dec.codeP_verified }
    (Proof.Rsa.RISCV64.Scrub.pkcs1DecryptOut _)),
  Spec.RsaPkcs1Enc.encryptRandomApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.RsaPkcs1Enc.RISCV64.Random.code
    verified := Proof.RsaPkcs1Enc.RISCV64.Rnd.code_verified }
    (Proof.Rsa.RISCV64.Scrub.pkcs1EncryptRandomOut _))]

end VG.Artifacts.RsaPkcs1Enc.RISCV64
