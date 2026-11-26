module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cfb.Contract
public import VerifiedGarbage.Spec.Cfb.Final
import VerifiedGarbage.Proof.Aes.RISCV64.Scrub
import VerifiedGarbage.Impl.Aes.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on RISC-V -/

namespace VG.Artifacts.AesCfb.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Cfb.aesEncryptApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.cfbEncrypt
    verified := Proof.Aes.RISCV64.Scrub.cfbEncrypt_scrubbed },
  Spec.Cfb.aesDecryptApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.cfbDecrypt
    verified := Proof.Aes.RISCV64.Scrub.cfbDecrypt_scrubbed },
  Spec.Cfb.aesEncryptFinalApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.cfbEncryptFinal
    verified := Proof.Aes.RISCV64.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Cfb.aesDecryptFinalApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.cfbDecryptFinal
    verified := Proof.Aes.RISCV64.Scrub.cfbDecryptFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.AesCfb.RISCV64
