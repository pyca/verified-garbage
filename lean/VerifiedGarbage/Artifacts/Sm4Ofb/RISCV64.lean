module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Ofb
public import VerifiedGarbage.Spec.Sm4.OfbFinal
import VerifiedGarbage.Proof.Sm4.RISCV64.Scrub
import VerifiedGarbage.Impl.Sm4.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
import VerifiedGarbage.Proof.Sm4.RISCV64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-OFB on RISC-V -/

namespace VG.Artifacts.Sm4Ofb.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Sm4.ofbApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.ofb
    verified := Proof.Sm4.RISCV64.Scrub.ofb_scrubbed },
  Spec.Sm4.ofbFinalApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.ofbFinal
    verified := Proof.Sm4.RISCV64.Scrub.ofbFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sm4Ofb.RISCV64
