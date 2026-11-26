module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Contract
import VerifiedGarbage.Proof.Seed.RISCV64.Scrub
import VerifiedGarbage.Impl.Seed.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED on RISC-V -/

namespace VG.Artifacts.Seed.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Seed.expandKeyApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.Fn.expandKey
    verified := Proof.Seed.RISCV64.Scrub.expandKey_scrubbed },
  Spec.Seed.ecbEncryptApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.Fn.ecbEncrypt
    verified := Proof.Seed.RISCV64.Scrub.ecbEncrypt_scrubbed },
  Spec.Seed.ecbDecryptApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.Fn.ecbDecrypt
    verified := Proof.Seed.RISCV64.Scrub.ecbDecrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Seed.RISCV64
