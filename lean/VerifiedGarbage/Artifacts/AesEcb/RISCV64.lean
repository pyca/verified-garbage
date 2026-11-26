module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.AesEcb.Contract
import VerifiedGarbage.Proof.Aes.RISCV64.Scrub
import VerifiedGarbage.Impl.Aes.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-ECB (NIST SP 800-38A §6.1) on RISC-V -/

namespace VG.Artifacts.AesEcb.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.AesEcb.encryptApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.ecbEncrypt
    verified := Proof.Aes.RISCV64.Scrub.ecbEncrypt_scrubbed
    publicOutOk := Proof.Aes.RISCV64.Scrub.ecbEncrypt_public },
  Spec.AesEcb.decryptApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.ecbDecrypt
    verified := Proof.Aes.RISCV64.Scrub.ecbDecrypt_scrubbed
    publicOutOk := Proof.Aes.RISCV64.Scrub.ecbDecrypt_public }]

spec_apis artifacts

end VG.Artifacts.AesEcb.RISCV64
