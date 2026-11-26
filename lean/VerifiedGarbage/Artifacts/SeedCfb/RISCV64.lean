module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Cfb
public import VerifiedGarbage.Spec.Seed.CfbFinal
import VerifiedGarbage.Proof.Seed.RISCV64.Scrub
import VerifiedGarbage.Impl.Seed.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.RISCV64.ModesLit
import VerifiedGarbage.Proof.Seed.RISCV64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED-CFB128 on RISC-V -/

namespace VG.Artifacts.SeedCfb.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Seed.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.Fn.cfbEncrypt
    verified := Proof.Seed.RISCV64.Scrub.cfbEncrypt_scrubbed },
  Spec.Seed.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.Fn.cfbDecrypt
    verified := Proof.Seed.RISCV64.Scrub.cfbDecrypt_scrubbed },
  Spec.Seed.cfbEncryptFinalApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.Fn.cfbEncryptFinal
    verified := Proof.Seed.RISCV64.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Seed.cfbDecryptFinalApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.Fn.cfbDecryptFinal
    verified := Proof.Seed.RISCV64.Scrub.cfbDecryptFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.SeedCfb.RISCV64
