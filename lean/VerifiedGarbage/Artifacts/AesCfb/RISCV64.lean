module

public import VerifiedGarbage.Proof.Aes.RISCV64.Scrub
public import VerifiedGarbage.Impl.Aes.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesCfb.RISCV64

def artifacts : List Artifact := [
  Spec.Cfb.aesEncryptApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.cfbEncrypt
    verified := .scrubbed Proof.Aes.RISCV64.Scrub.cfbEncrypt_scrubbed },
  Spec.Cfb.aesDecryptApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.cfbDecrypt
    verified := .scrubbed Proof.Aes.RISCV64.Scrub.cfbDecrypt_scrubbed },
  Spec.Cfb.aesEncryptFinalApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.cfbEncryptFinal
    verified := .scrubbed Proof.Aes.RISCV64.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Cfb.aesDecryptFinalApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.cfbDecryptFinal
    verified := .scrubbed Proof.Aes.RISCV64.Scrub.cfbDecryptFinal_scrubbed }]

end VG.Artifacts.AesCfb.RISCV64
