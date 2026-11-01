module

public import VerifiedGarbage.Proof.Sm4.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit

/-! # SM4-OFB artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm4Ofb.RISCV64

def artifacts : List Artifact := [
  Spec.Sm4.ofbApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.ofb
    stack := 3232
    verified := Proof.Sm4.RISCV64.Modes.ofb_verified }]

end VG.Artifacts.Sm4Ofb.RISCV64
