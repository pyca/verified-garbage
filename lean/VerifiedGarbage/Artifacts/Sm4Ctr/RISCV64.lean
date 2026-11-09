module

public import VerifiedGarbage.Proof.Sm4.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Sm4.RISCV64.CtrFinal
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit

/-! # SM4-CTR artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm4Ctr.RISCV64

def artifacts : List Artifact := [
  Spec.Sm4.ctrApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.ctr
    stack := 3248
    verified := Proof.Sm4.RISCV64.Modes.ctr_verified },
  Spec.Sm4.ctrFinalApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 80 .a4 10 Impl.Sm4.RISCV64.ctrFinal
    stack := 3328
    verified := Proof.Sm4.RISCV64.CtrFinal.ctrFinal_framed }]

end VG.Artifacts.Sm4Ctr.RISCV64
