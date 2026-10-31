module

public import VerifiedGarbage.Proof.Seed.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.RISCV64.ModesLit

/-! # SEED-OFB artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.SeedOfb.RISCV64

def artifacts : List Artifact := [
  Spec.Seed.ofbApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.ofb
    stack := 1104
    verified := Proof.Seed.RISCV64.Modes.ofb_verified }]

end VG.Artifacts.SeedOfb.RISCV64
