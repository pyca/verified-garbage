module

public import VerifiedGarbage.Proof.AesEcb.RISCV64
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit

/-! # AES-ECB (NIST SP 800-38A §6.1) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesEcb.RISCV64

def artifacts : List Artifact := [
  Spec.AesEcb.encryptApi.artifact RISCV64.target {
    code := Proof.AesEcb.RISCV64.encrypt
    stack := 32
    verified := Proof.AesEcb.RISCV64.encrypt_verified },
  Spec.AesEcb.decryptApi.artifact RISCV64.target {
    code := Proof.AesEcb.RISCV64.decrypt
    stack := 32
    verified := Proof.AesEcb.RISCV64.decrypt_verified }]

end VG.Artifacts.AesEcb.RISCV64
