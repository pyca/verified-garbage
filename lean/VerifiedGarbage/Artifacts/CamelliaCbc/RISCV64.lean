module

public import VerifiedGarbage.Proof.Camellia.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit

/-! # Camellia-CBC artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.CamelliaCbc.RISCV64

def artifacts : List Artifact := [
  Spec.Camellia.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.cbcEncryptChained
    stack := 3248
    verified := Proof.Camellia.RISCV64.Modes.cbcEncryptChained_verified },
  Spec.Camellia.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.cbcDecryptChained
    stack := 3248
    verified := Proof.Camellia.RISCV64.Modes.cbcDecryptChained_verified }]

end VG.Artifacts.CamelliaCbc.RISCV64
