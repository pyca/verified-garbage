module

public import VerifiedGarbage.Proof.AesCfb.RISCV64.Verified
public import VerifiedGarbage.Proof.AesCfb.RISCV64.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesCfb.RISCV64

open VG.Proof.AesCfb.RISCV64

def artifacts : List Artifact := [
  Spec.Cfb.aesEncryptApi.artifact RISCV64.target {
    code := Impl.AesCfb.RISCV64.encrypt
    verified := Proof.AesCfb.encrypt_keyed encrypt_verified },
  Spec.Cfb.aesDecryptApi.artifact RISCV64.target {
    code := Impl.AesCfb.RISCV64.decrypt
    verified := Proof.AesCfb.decrypt_keyed decrypt_verified },
  Spec.Cfb.aesEncryptFinalApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 64 .a6 8 Impl.AesCfb.RISCV64.encryptFinal
    stack := 64
    verified := Proof.AesCfb.encryptFinal_keyed Final.encryptFinal_framed },
  Spec.Cfb.aesDecryptFinalApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 64 .a6 8 Impl.AesCfb.RISCV64.decryptFinal
    stack := 64
    verified := Proof.AesCfb.decryptFinal_keyed Final.decryptFinal_framed }]

end VG.Artifacts.AesCfb.RISCV64
