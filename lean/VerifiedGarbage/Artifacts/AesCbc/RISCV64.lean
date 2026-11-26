module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cbc.Contract
import VerifiedGarbage.Proof.Aes.RISCV64.Scrub
import VerifiedGarbage.Impl.Aes.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesCbc.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CBC (NIST SP 800-38A §6.2) on RISC-V -/

namespace VG.Artifacts.AesCbc.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Cbc.aesEncryptApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.cbcEncrypt
    verified := Proof.Aes.RISCV64.Scrub.cbcEncrypt_scrubbed
    publicOutOk := Proof.Aes.RISCV64.Scrub.cbcEncrypt_public },
  Spec.Cbc.aesDecryptApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.cbcDecrypt
    verified := Proof.Aes.RISCV64.Scrub.cbcDecrypt_scrubbed
    publicOutOk := Proof.Aes.RISCV64.Scrub.cbcDecrypt_public }]

spec_apis artifacts

end VG.Artifacts.AesCbc.RISCV64
