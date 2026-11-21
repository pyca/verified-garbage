module

public import VerifiedGarbage.Proof.Sm4.RISCV64.Scrub
public import VerifiedGarbage.Impl.Sm4.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Sm4.RISCV64.Lit

/-! # SM4 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm4.RISCV64

def artifacts : List Artifact := [
  Spec.Sm4.expandKeyApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.expandKey
    verified := Proof.Sm4.RISCV64.Scrub.expandKey_scrubbed },
  Spec.Sm4.ecbEncryptApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.ecbEncrypt
    verified := Proof.Sm4.RISCV64.Scrub.ecbEncrypt_scrubbed },
  Spec.Sm4.ecbDecryptApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.ecbDecrypt
    verified := Proof.Sm4.RISCV64.Scrub.ecbDecrypt_scrubbed }]

end VG.Artifacts.Sm4.RISCV64
