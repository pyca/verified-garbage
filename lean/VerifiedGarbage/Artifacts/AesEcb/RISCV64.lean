module

public import VerifiedGarbage.Proof.Aes.RISCV64.Scrub
public import VerifiedGarbage.Impl.Aes.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit

/-! # AES-ECB (NIST SP 800-38A §6.1) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesEcb.RISCV64

def artifacts : List Artifact := [
  Spec.AesEcb.encryptApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.ecbEncrypt
    verified := Proof.Aes.RISCV64.Scrub.ecbEncrypt_scrubbed },
  Spec.AesEcb.decryptApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.ecbDecrypt
    verified := Proof.Aes.RISCV64.Scrub.ecbDecrypt_scrubbed }]

end VG.Artifacts.AesEcb.RISCV64
