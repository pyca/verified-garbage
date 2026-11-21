module

public import VerifiedGarbage.Proof.Sm4.RISCV64.Scrub
public import VerifiedGarbage.Impl.Sm4.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
import VerifiedGarbage.Proof.Sm4.RISCV64.FbFinalLit

/-! # SM4-CFB128 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.RISCV64

def artifacts : List Artifact := [
  Spec.Sm4.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.cfbEncrypt
    verified := Proof.Sm4.RISCV64.Scrub.cfbEncrypt_scrubbed },
  Spec.Sm4.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.cfbDecrypt
    verified := Proof.Sm4.RISCV64.Scrub.cfbDecrypt_scrubbed },
  Spec.Sm4.cfbEncryptFinalApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.cfbEncryptFinal
    verified := Proof.Sm4.RISCV64.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Sm4.cfbDecryptFinalApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.cfbDecryptFinal
    verified := Proof.Sm4.RISCV64.Scrub.cfbDecryptFinal_scrubbed }]

end VG.Artifacts.Sm4Cfb.RISCV64
