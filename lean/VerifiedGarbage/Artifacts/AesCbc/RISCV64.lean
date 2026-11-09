module

public import VerifiedGarbage.Proof.AesCbc.RISCV64.Wiped
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.AesCbc.RISCV64.Lit

/-! # AES-CBC (NIST SP 800-38A §6.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesCbc.RISCV64

open VG.Proof.AesCbc.RISCV64

def artifacts : List Artifact := [
  Spec.Cbc.aesEncryptApi.artifact RISCV64.target {
    code := Wiped.encrypt
    stack := 32
    verified := Wiped.encrypt_verified },
  Spec.Cbc.aesDecryptApi.artifact RISCV64.target {
    code := Wiped.decrypt
    stack := 32
    verified := Wiped.decrypt_verified }]

end VG.Artifacts.AesCbc.RISCV64
