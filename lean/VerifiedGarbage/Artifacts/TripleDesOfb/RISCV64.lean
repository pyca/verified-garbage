module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Ofb
public import VerifiedGarbage.Spec.TripleDes.OfbFinal
import VerifiedGarbage.Proof.TripleDes.RISCV64.Scrub
import VerifiedGarbage.Impl.TripleDes.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit
import VerifiedGarbage.Proof.TripleDes.RISCV64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-OFB on RISC-V -/

namespace VG.Artifacts.TripleDesOfb.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.TripleDes.ofbApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.ofb
    verified := Proof.TripleDes.RISCV64.Scrub.ofb_scrubbed },
  Spec.TripleDes.ofbFinalApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.ofbFinal
    verified := Proof.TripleDes.RISCV64.Scrub.ofbFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.TripleDesOfb.RISCV64
