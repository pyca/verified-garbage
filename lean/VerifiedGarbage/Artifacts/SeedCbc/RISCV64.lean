module

public import VerifiedGarbage.Proof.Seed.RISCV64.Scrub
public import VerifiedGarbage.Impl.Seed.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Seed.RISCV64.ModesLit

/-! # SEED-CBC on RISC-V -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.RISCV64

def artifacts : List Artifact := [
  Spec.Seed.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.Fn.cbcEncryptChained
    verified := .scrubbed Proof.Seed.RISCV64.Scrub.cbcEncryptChained_scrubbed },
  Spec.Seed.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.Fn.cbcDecryptChained
    verified := .scrubbed Proof.Seed.RISCV64.Scrub.cbcDecryptChained_scrubbed }]

end VG.Artifacts.SeedCbc.RISCV64
