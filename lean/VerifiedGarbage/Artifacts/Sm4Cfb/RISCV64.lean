module

public import VerifiedGarbage.Proof.Sm4.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit

/-! # SM4-CFB128 artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.RISCV64

def artifacts : List Artifact := [
  Spec.Sm4.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.cfbEncrypt
    stack := 3232
    verified := Proof.Sm4.RISCV64.Modes.cfbEncrypt_verified },
  Spec.Sm4.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.cfbDecrypt
    stack := 3232
    verified := Proof.Sm4.RISCV64.Modes.cfbDecrypt_verified }]

end VG.Artifacts.Sm4Cfb.RISCV64
