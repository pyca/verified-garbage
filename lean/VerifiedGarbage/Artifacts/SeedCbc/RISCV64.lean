module

public import VerifiedGarbage.Proof.Seed.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.RISCV64.ModesLit

/-! # SEED-CBC artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.RISCV64

def artifacts : List Artifact := [
  Spec.Seed.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.cbcEncryptChained
    stack := 1104
    verified := Proof.Seed.RISCV64.Modes.cbcEncryptChained_verified },
  Spec.Seed.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.cbcDecryptChained
    stack := 1104
    verified := Proof.Seed.RISCV64.Modes.cbcDecryptChained_verified }]

end VG.Artifacts.SeedCbc.RISCV64
