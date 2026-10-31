module

public import VerifiedGarbage.Proof.AesCfb.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesCfb.RISCV64

open VG.Proof.AesCfb.RISCV64

def artifacts : List Artifact := [
  Spec.Cfb.aesEncryptApi.artifact RISCV64.target {
    code := Impl.AesCfb.RISCV64.encrypt
    verified := encrypt_verified },
  Spec.Cfb.aesDecryptApi.artifact RISCV64.target {
    code := Impl.AesCfb.RISCV64.decrypt
    verified := decrypt_verified }]

end VG.Artifacts.AesCfb.RISCV64
