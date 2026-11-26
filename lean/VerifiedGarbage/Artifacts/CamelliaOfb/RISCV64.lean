module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Ofb
public import VerifiedGarbage.Spec.Camellia.OfbFinal
import VerifiedGarbage.Proof.Camellia.RISCV64.Scrub
import VerifiedGarbage.Impl.Camellia.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit
import VerifiedGarbage.Proof.Camellia.RISCV64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia-OFB on RISC-V -/

namespace VG.Artifacts.CamelliaOfb.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Camellia.ofbApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.ofb
    verified := Proof.Camellia.RISCV64.Scrub.ofb_scrubbed },
  Spec.Camellia.ofbFinalApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.ofbFinal
    verified := Proof.Camellia.RISCV64.Scrub.ofbFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.CamelliaOfb.RISCV64
