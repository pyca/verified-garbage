module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.RISCV64.Compress
import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.CT
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Argon2.RISCV64.Scrub
import VerifiedGarbage.Impl.Argon2.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Argon2 (RFC 9106) on RISC-V -/

namespace VG.Artifacts.Argon2.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Argon2.deriveApi.artifact RISCV64.target {
    code := Impl.Argon2.RISCV64.Fn.derive
    verified := Proof.Argon2.RISCV64.Scrub.derive_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Argon2.RISCV64
