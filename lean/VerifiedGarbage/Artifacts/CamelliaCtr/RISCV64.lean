module

public import VerifiedGarbage.Proof.Camellia.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Camellia.RISCV64.CtrFinal
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit

/-! # Camellia-CTR artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.RISCV64

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.ctr
    stack := 3264
    verified := Proof.Camellia.RISCV64.Modes.ctr_verified },
  Spec.Camellia.ctrFinalApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 80 .a5 10 Impl.Camellia.RISCV64.ctrFinal
    stack := 3344
    verified := Proof.Camellia.RISCV64.CtrFinal.ctrFinal_framed }]

end VG.Artifacts.CamelliaCtr.RISCV64
