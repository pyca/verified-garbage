module

public import VerifiedGarbage.Proof.Sm4.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit

/-! # SM4-CBC artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm4Cbc.RISCV64

def artifacts : List Artifact := [
  Spec.Sm4.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.cbcEncryptChained
    stack := 3232
    verified := Proof.Sm4.RISCV64.Modes.cbcEncryptChained_verified },
  Spec.Sm4.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.cbcDecryptChained
    stack := 3232
    verified := Proof.Sm4.RISCV64.Modes.cbcDecryptChained_verified }]

end VG.Artifacts.Sm4Cbc.RISCV64
