module

public import VerifiedGarbage.Proof.Camellia.RISCV64.Scrub
public import VerifiedGarbage.Impl.Camellia.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit

/-! # Camellia-CTR on RISC-V -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.RISCV64

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.ctr
    verified := Proof.Camellia.RISCV64.Scrub.ctr_scrubbed },
  Spec.Camellia.ctrFinalApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.ctrFinal
    verified := Proof.Camellia.RISCV64.Scrub.ctrFinal_scrubbed }]

end VG.Artifacts.CamelliaCtr.RISCV64
