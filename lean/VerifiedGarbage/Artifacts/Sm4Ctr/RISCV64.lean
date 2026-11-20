module

public import VerifiedGarbage.Proof.Sm4.RISCV64.Scrub
public import VerifiedGarbage.Impl.Sm4.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit

/-! # SM4-CTR on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm4Ctr.RISCV64

def artifacts : List Artifact := [
  Spec.Sm4.ctrApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.ctr
    verified := .scrubbed Proof.Sm4.RISCV64.Scrub.ctr_scrubbed },
  Spec.Sm4.ctrFinalApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.ctrFinal
    verified := .scrubbed Proof.Sm4.RISCV64.Scrub.ctrFinal_scrubbed }]

end VG.Artifacts.Sm4Ctr.RISCV64
