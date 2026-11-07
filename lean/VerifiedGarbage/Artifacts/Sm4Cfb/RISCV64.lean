module

public import VerifiedGarbage.Proof.Sm4.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Sm4.RISCV64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
import VerifiedGarbage.Proof.Sm4.RISCV64.FbFinalLit

/-! # SM4-CFB128 artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.RISCV64

def artifacts : List Artifact := [
  Spec.Sm4.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.cfbEncrypt
    stack := 3248
    verified := Proof.Sm4.RISCV64.Modes.cfbEncrypt_verified },
  Spec.Sm4.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.cfbDecrypt
    stack := 3248
    verified := Proof.Sm4.RISCV64.Modes.cfbDecrypt_verified },
  Spec.Sm4.cfbEncryptFinalApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.cfbEncryptFinal
    stack := 3248
    verified := Proof.Sm4.RISCV64.Modes.cfbEncryptFinal_verified },
  Spec.Sm4.cfbDecryptFinalApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.cfbDecryptFinal
    stack := 3248
    verified := Proof.Sm4.RISCV64.Modes.cfbDecryptFinal_verified }]

end VG.Artifacts.Sm4Cfb.RISCV64
