module

public import VerifiedGarbage.Proof.Camellia.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit

/-! # Camellia-CFB128 artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.RISCV64

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.cfbEncrypt
    stack := 3248
    verified := Proof.Camellia.RISCV64.Modes.cfbEncrypt_verified },
  Spec.Camellia.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.cfbDecrypt
    stack := 3248
    verified := Proof.Camellia.RISCV64.Modes.cfbDecrypt_verified }]

end VG.Artifacts.CamelliaCfb.RISCV64
