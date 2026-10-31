module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Key.Verified
public import VerifiedGarbage.Proof.TripleDes.RISCV64.EcbVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.RISCV64.FunctionsLit

/-! # Triple DES on RISC-V -/

@[expose] public section

namespace VG.Artifacts.TripleDes.RISCV64

def artifacts : List Artifact := [
  Spec.TripleDes.expandKeyApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Key.expandKey
    verified := Proof.TripleDes.RISCV64.Key.verified },
  Spec.TripleDes.ecbEncryptApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Ecb.encrypt
    stack := 944
    verified := Proof.TripleDes.RISCV64.Ecb.encrypt_verified },
  Spec.TripleDes.ecbDecryptApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Ecb.decrypt
    stack := 944
    verified := Proof.TripleDes.RISCV64.Ecb.decrypt_verified }]

end VG.Artifacts.TripleDes.RISCV64
