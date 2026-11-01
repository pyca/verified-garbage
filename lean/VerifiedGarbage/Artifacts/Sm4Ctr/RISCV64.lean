module

public import VerifiedGarbage.Proof.Sm4.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit

/-! # SM4-CTR artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm4Ctr.RISCV64

def artifacts : List Artifact := [
  Spec.Sm4.ctrApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.ctr
    stack := 3232
    verified := Proof.Sm4.RISCV64.Modes.ctr_verified }]

end VG.Artifacts.Sm4Ctr.RISCV64
