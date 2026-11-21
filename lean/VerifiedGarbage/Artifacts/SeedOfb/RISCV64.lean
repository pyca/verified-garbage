module

public import VerifiedGarbage.Proof.Seed.RISCV64.Scrub
public import VerifiedGarbage.Impl.Seed.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Seed.RISCV64.ModesLit
import VerifiedGarbage.Proof.Seed.RISCV64.FbFinalLit

/-! # SEED-OFB on RISC-V -/

@[expose] public section

namespace VG.Artifacts.SeedOfb.RISCV64

def artifacts : List Artifact := [
  Spec.Seed.ofbApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.Fn.ofb
    verified := Proof.Seed.RISCV64.Scrub.ofb_scrubbed },
  Spec.Seed.ofbFinalApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.Fn.ofbFinal
    verified := Proof.Seed.RISCV64.Scrub.ofbFinal_scrubbed }]

end VG.Artifacts.SeedOfb.RISCV64
