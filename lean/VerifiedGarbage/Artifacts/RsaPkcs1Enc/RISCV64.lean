module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.EncVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # PKCS #1 v1.5 encryption with a precomputed RSA public key, on RISC-V -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Enc.RISCV64

def artifacts : List Artifact := [
  Spec.RsaPkcs1Enc.encryptPrecomputedApi.artifact RISCV64.target {
    code := Impl.RsaPkcs1Enc.RISCV64.Precomputed.code
    stack := 2128
    verified := Proof.RsaPkcs1Enc.RISCV64.Enc.code_verified }]

end VG.Artifacts.RsaPkcs1Enc.RISCV64
