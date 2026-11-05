module

public import VerifiedGarbage.Proof.AesCbc.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.AesCbc.RISCV64.Lit

/-! # AES-CBC (NIST SP 800-38A §6.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesCbc.RISCV64

open VG.Proof.AesCbc.RISCV64

def artifacts : List Artifact := [
  Spec.Cbc.aesEncryptApi.artifact RISCV64.target {
    code := Impl.AesCbc.RISCV64.encrypt
    verified := Proof.AesCbc.encrypt_keyed encrypt_verified },
  Spec.Cbc.aesDecryptApi.artifact RISCV64.target {
    code := Impl.AesCbc.RISCV64.decrypt
    verified := Proof.AesCbc.decrypt_keyed decrypt_verified }]

end VG.Artifacts.AesCbc.RISCV64
