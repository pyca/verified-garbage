module

public import VerifiedGarbage.Proof.Seed.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Seed.RISCV64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Seed.RISCV64.ModesLit
import VerifiedGarbage.Proof.Seed.RISCV64.FbFinalLit

/-! # SEED-OFB artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.SeedOfb.RISCV64

def artifacts : List Artifact := [
  Spec.Seed.ofbApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.ofb
    stack := 1120
    verified := Proof.Seed.RISCV64.Modes.ofb_verified },
  Spec.Seed.ofbFinalApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.ofbFinal
    stack := 1120
    verified := Proof.Seed.RISCV64.Modes.ofbFinal_verified }]

end VG.Artifacts.SeedOfb.RISCV64
