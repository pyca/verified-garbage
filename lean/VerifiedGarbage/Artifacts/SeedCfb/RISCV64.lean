module

public import VerifiedGarbage.Proof.Seed.RISCV64.Scrub
public import VerifiedGarbage.Impl.Seed.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Seed.RISCV64.ModesLit
import VerifiedGarbage.Proof.Seed.RISCV64.FbFinalLit

/-! # SEED-CFB128 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.SeedCfb.RISCV64

def artifacts : List Artifact := [
  Spec.Seed.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.Fn.cfbEncrypt
    verified := .scrubbed Proof.Seed.RISCV64.Scrub.cfbEncrypt_scrubbed },
  Spec.Seed.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.Fn.cfbDecrypt
    verified := .scrubbed Proof.Seed.RISCV64.Scrub.cfbDecrypt_scrubbed },
  Spec.Seed.cfbEncryptFinalApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.Fn.cfbEncryptFinal
    verified := .scrubbed Proof.Seed.RISCV64.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Seed.cfbDecryptFinalApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.Fn.cfbDecryptFinal
    verified := .scrubbed Proof.Seed.RISCV64.Scrub.cfbDecryptFinal_scrubbed }]

end VG.Artifacts.SeedCfb.RISCV64
