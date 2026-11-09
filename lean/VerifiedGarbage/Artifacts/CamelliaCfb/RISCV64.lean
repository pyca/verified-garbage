module

public import VerifiedGarbage.Proof.Camellia.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Camellia.RISCV64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit
import VerifiedGarbage.Proof.Camellia.RISCV64.FbFinalLit

/-! # Camellia-CFB128 artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.RISCV64

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.cfbEncrypt
    stack := 3264
    verified := Proof.Camellia.RISCV64.Modes.cfbEncrypt_verified },
  Spec.Camellia.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.cfbDecrypt
    stack := 3264
    verified := Proof.Camellia.RISCV64.Modes.cfbDecrypt_verified },
  Spec.Camellia.cfbEncryptFinalApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.cfbEncryptFinal
    stack := 3264
    verified := Proof.Camellia.RISCV64.Modes.cfbEncryptFinal_verified },
  Spec.Camellia.cfbDecryptFinalApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.cfbDecryptFinal
    stack := 3264
    verified := Proof.Camellia.RISCV64.Modes.cfbDecryptFinal_verified }]

end VG.Artifacts.CamelliaCfb.RISCV64
