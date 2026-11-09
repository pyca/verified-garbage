module

public import VerifiedGarbage.Proof.AesCfb8.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.AesCfb8.RISCV64.Lit

/-! # AES-CFB8 (NIST SP 800-38A §6.3) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesCfb8.RISCV64

open VG.Proof.AesCfb8.RISCV64

def artifacts : List Artifact := [
  Spec.Cfb8.aesEncryptApi.artifact RISCV64.target {
    code := Impl.AesCfb8.RISCV64.encrypt
    verified := Proof.AesCfb8.encrypt_keyed encrypt_verified },
  Spec.Cfb8.aesDecryptApi.artifact RISCV64.target {
    code := Impl.AesCfb8.RISCV64.decrypt
    verified := Proof.AesCfb8.decrypt_keyed decrypt_verified }]

end VG.Artifacts.AesCfb8.RISCV64
