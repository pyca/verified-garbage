module

public import VerifiedGarbage.Proof.Camellia.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit

/-! # Camellia-CTR artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.RISCV64

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.ctr
    stack := 3248
    verified := Proof.Camellia.RISCV64.Modes.ctr_verified }]

end VG.Artifacts.CamelliaCtr.RISCV64
