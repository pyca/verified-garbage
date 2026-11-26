module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cast5.Ofb
public import VerifiedGarbage.Spec.Cast5.OfbFinal
import VerifiedGarbage.Proof.Cast5.RISCV64.Scrub
import VerifiedGarbage.Impl.Cast5.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Cast5.RISCV64.ModesLit
import VerifiedGarbage.Proof.Cast5.RISCV64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # CAST5-OFB on RISC-V -/

namespace VG.Artifacts.Cast5Ofb.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Cast5.ofbApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.Fn.ofb
    verified := Proof.Cast5.RISCV64.Scrub.ofb_scrubbed },
  Spec.Cast5.ofbFinalApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.Fn.ofbFinal
    verified := Proof.Cast5.RISCV64.Scrub.ofbFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Cast5Ofb.RISCV64
