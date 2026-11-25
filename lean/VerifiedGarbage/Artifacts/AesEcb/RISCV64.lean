module

public import VerifiedGarbage.Proof.Aes.RISCV64.Scrub
public import VerifiedGarbage.Impl.Aes.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit

/-! # AES-ECB (NIST SP 800-38A §6.1) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesEcb.RISCV64

def artifacts : List (Artifact RISCV64.target) := [
  Spec.AesEcb.encryptApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.ecbEncrypt
    verified := Proof.Aes.RISCV64.Scrub.ecbEncrypt_scrubbed
    publicOutOk := Proof.Aes.RISCV64.Scrub.ecbEncrypt_public },
  Spec.AesEcb.decryptApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.ecbDecrypt
    verified := Proof.Aes.RISCV64.Scrub.ecbDecrypt_scrubbed
    publicOutOk := Proof.Aes.RISCV64.Scrub.ecbDecrypt_public }]

end VG.Artifacts.AesEcb.RISCV64
