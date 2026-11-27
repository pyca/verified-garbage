module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Cbc
import VerifiedGarbage.Proof.Seed.RISCV64.Scrub
import VerifiedGarbage.Impl.Seed.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.RISCV64.ModesLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED-CBC on RISC-V -/

namespace VG.Artifacts.SeedCbc.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Seed.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.Fn.cbcEncryptChained
    verified := Proof.Seed.RISCV64.Scrub.cbcEncryptChained_scrubbed },
  Spec.Seed.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.Fn.cbcDecryptChained
    verified := Proof.Seed.RISCV64.Scrub.cbcDecryptChained_scrubbed }]

spec_apis artifacts

end VG.Artifacts.SeedCbc.RISCV64
