module

public import VerifiedGarbage.Proof.Cast5.RISCV64.Scrub
public import VerifiedGarbage.Impl.Cast5.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Cast5.RISCV64.ModesLit
import VerifiedGarbage.Proof.Cast5.RISCV64.FbFinalLit

/-! # CAST5-OFB on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Cast5Ofb.RISCV64

def artifacts : List Artifact := [
  Spec.Cast5.ofbApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.Fn.ofb
    verified := Proof.Cast5.RISCV64.Scrub.ofb_scrubbed },
  Spec.Cast5.ofbFinalApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.Fn.ofbFinal
    verified := Proof.Cast5.RISCV64.Scrub.ofbFinal_scrubbed }]

end VG.Artifacts.Cast5Ofb.RISCV64
