module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Scrub
import VerifiedGarbage.Impl.Pbkdf2.Whole.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # PBKDF2-HMAC-SHA-512 (RFC 8018) on RISC-V -/

namespace VG.Artifacts.Pbkdf2Sha512.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Hmac.sha512I.pbkdf2Api.artifact RISCV64.target {
    code := Impl.Pbkdf2.Whole.RISCV64.Fn.pbkdf2 Proof.Pbkdf2.Whole.RISCV64.Sha512.F
    verified := Proof.Pbkdf2.Whole.RISCV64.Scrub.sha512_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Pbkdf2Sha512.RISCV64
