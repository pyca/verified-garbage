module

public import VerifiedGarbage.Proof.Aes.RISCV64.Scrub
public import VerifiedGarbage.Impl.Aes.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.AesCbc.RISCV64.Lit

/-! # AES-CBC (NIST SP 800-38A §6.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesCbc.RISCV64

def artifacts : List Artifact := [
  Spec.Cbc.aesEncryptApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.cbcEncrypt
    verified := .scrubbed Proof.Aes.RISCV64.Scrub.cbcEncrypt_scrubbed },
  Spec.Cbc.aesDecryptApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.cbcDecrypt
    verified := .scrubbed Proof.Aes.RISCV64.Scrub.cbcDecrypt_scrubbed }]

end VG.Artifacts.AesCbc.RISCV64
