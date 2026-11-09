module

public import VerifiedGarbage.Proof.Cast5.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Cast5.RISCV64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Cast5.RISCV64.ModesLit
import VerifiedGarbage.Proof.Cast5.RISCV64.FbFinalLit

/-! # CAST5-OFB artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.Cast5Ofb.RISCV64

def artifacts : List Artifact := [
  Spec.Cast5.ofbApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.ofb
    stack := 128
    verified := Proof.Cast5.ofb_keyed Proof.Cast5.RISCV64.Modes.ofb_verified },
  Spec.Cast5.ofbFinalApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.ofbFinal
    stack := 128
    verified := Proof.Cast5.ofbFinal_keyed Proof.Cast5.RISCV64.Modes.ofbFinal_verified }]

end VG.Artifacts.Cast5Ofb.RISCV64
