module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Siv.Contract
import VerifiedGarbage.Proof.AesSiv.RISCV64.Init
import VerifiedGarbage.Proof.AesSiv.RISCV64.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-SIV (RFC 5297) on RISC-V -/

namespace VG.Artifacts.AesSiv.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Siv.initApi.artifact RISCV64.target {
    code := Impl.AesSiv.RISCV64.Fn.init
    verified := Proof.AesSiv.RISCV64.init_scrubbed },
  Spec.Siv.encryptApi.artifact RISCV64.target {
    code := Impl.AesSiv.RISCV64.Fn.encrypt
    verified := Proof.AesSiv.RISCV64.Scrub.encrypt_scrubbed },
  Spec.Siv.decryptApi.artifact RISCV64.target {
    code := Impl.AesSiv.RISCV64.Fn.decrypt
    verified := Proof.AesSiv.RISCV64.Scrub.decrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.AesSiv.RISCV64
