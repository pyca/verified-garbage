module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cfb8.Contract
import VerifiedGarbage.Proof.Aes.RISCV64.Scrub
import VerifiedGarbage.Impl.Aes.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesCfb8.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CFB8 (NIST SP 800-38A §6.3) on RISC-V -/

namespace VG.Artifacts.AesCfb8.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Cfb8.aesEncryptApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.cfb8Encrypt
    verified := Proof.Aes.RISCV64.Scrub.cfb8Encrypt_scrubbed },
  Spec.Cfb8.aesDecryptApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.cfb8Decrypt
    verified := Proof.Aes.RISCV64.Scrub.cfb8Decrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.AesCfb8.RISCV64
