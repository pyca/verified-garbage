module

public import VerifiedGarbage.Proof.Seed.RISCV64.Scrub
public import VerifiedGarbage.Impl.Seed.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Seed.RISCV64.Lit

/-! # SEED on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Seed.RISCV64

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.Fn.expandKey
    verified := .scrubbed Proof.Seed.RISCV64.Scrub.expandKey_scrubbed },
  Spec.Seed.ecbEncryptApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.Fn.ecbEncrypt
    verified := .scrubbed Proof.Seed.RISCV64.Scrub.ecbEncrypt_scrubbed },
  Spec.Seed.ecbDecryptApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.Fn.ecbDecrypt
    verified := .scrubbed Proof.Seed.RISCV64.Scrub.ecbDecrypt_scrubbed }]

end VG.Artifacts.Seed.RISCV64
