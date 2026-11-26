module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Ofb
public import VerifiedGarbage.Spec.Seed.OfbFinal
import VerifiedGarbage.Proof.Seed.RISCV64.Scrub
import VerifiedGarbage.Impl.Seed.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.RISCV64.ModesLit
import VerifiedGarbage.Proof.Seed.RISCV64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED-OFB on RISC-V -/

namespace VG.Artifacts.SeedOfb.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Seed.ofbApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.Fn.ofb
    verified := Proof.Seed.RISCV64.Scrub.ofb_scrubbed },
  Spec.Seed.ofbFinalApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.Fn.ofbFinal
    verified := Proof.Seed.RISCV64.Scrub.ofbFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.SeedOfb.RISCV64
