module

public import VerifiedGarbage.Proof.Cast5.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Cast5.RISCV64.ModesLit

/-! # CAST5-OFB artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.Cast5Ofb.RISCV64

def artifacts : List Artifact := [
  Spec.Cast5.ofbApi.artifact RISCV64.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.RISCV64.ofb
    stack := 128
    verified := Proof.Cast5.RISCV64.Modes.ofb_verified }]

end VG.Artifacts.Cast5Ofb.RISCV64
