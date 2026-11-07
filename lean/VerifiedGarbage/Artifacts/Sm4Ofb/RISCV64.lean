module

public import VerifiedGarbage.Proof.Sm4.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Sm4.RISCV64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
import VerifiedGarbage.Proof.Sm4.RISCV64.FbFinalLit

/-! # SM4-OFB artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm4Ofb.RISCV64

def artifacts : List Artifact := [
  Spec.Sm4.ofbApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.ofb
    stack := 3248
    verified := Proof.Sm4.RISCV64.Modes.ofb_verified },
  Spec.Sm4.ofbFinalApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.ofbFinal
    stack := 3248
    verified := Proof.Sm4.RISCV64.Modes.ofbFinal_verified }]

end VG.Artifacts.Sm4Ofb.RISCV64
