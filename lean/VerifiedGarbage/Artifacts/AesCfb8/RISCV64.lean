module

public import VerifiedGarbage.Proof.Aes.RISCV64.Scrub
public import VerifiedGarbage.Impl.Aes.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.AesCfb8.RISCV64.Lit

/-! # AES-CFB8 (NIST SP 800-38A §6.3) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesCfb8.RISCV64

def artifacts : List Artifact := [
  Spec.Cfb8.aesEncryptApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.cfb8Encrypt
    verified := .scrubbed Proof.Aes.RISCV64.Scrub.cfb8Encrypt_scrubbed },
  Spec.Cfb8.aesDecryptApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.cfb8Decrypt
    verified := .scrubbed Proof.Aes.RISCV64.Scrub.cfb8Decrypt_scrubbed }]

end VG.Artifacts.AesCfb8.RISCV64
