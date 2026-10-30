module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.EcbVerified
public import VerifiedGarbage.Proof.Blowfish.RISCV64.KeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blowfish.RISCV64.Lit

/-! # Blowfish on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Blowfish.RISCV64

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.expandKey
    stack := 4176
    verified := Proof.Blowfish.RISCV64.expandKey_verified },
  Spec.Blowfish.ecbEncryptApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.encrypt
    stack := 4176
    verified := Proof.Blowfish.RISCV64.encrypt_verified },
  Spec.Blowfish.ecbDecryptApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.decrypt
    stack := 4176
    verified := Proof.Blowfish.RISCV64.decrypt_verified }]

end VG.Artifacts.Blowfish.RISCV64
