module

public import VerifiedGarbage.Proof.Cast5.RISCV64.EcbVerified
public import VerifiedGarbage.Proof.Cast5.RISCV64.KeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Cast5.RISCV64.Lit

/-! # CAST5 key expansion and ECB on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Cast5.RISCV64

def artifacts : List Artifact := [
  Spec.Cast5.expandKeyApi.artifact RISCV64.target {
    consts := Impl.Cast5.keyConsts
    code := Impl.Cast5.RISCV64.expandKey
    verified := Proof.Cast5.RISCV64.expandKey_verified },
  Spec.Cast5.ecbEncryptApi.artifact RISCV64.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.RISCV64.ecbEncrypt
    verified := Proof.Cast5.RISCV64.ecbEncrypt_verified },
  Spec.Cast5.ecbDecryptApi.artifact RISCV64.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.RISCV64.ecbDecrypt
    verified := Proof.Cast5.RISCV64.ecbDecrypt_verified }]

end VG.Artifacts.Cast5.RISCV64
