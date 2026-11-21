module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Scrub
public import VerifiedGarbage.Impl.Pbkdf2.Whole.RISCV64.Fn
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # PBKDF2-HMAC-SHA-256 (RFC 8018) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha256.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.sha256I.pbkdf2Api.artifact RISCV64.target {
    code := Impl.Pbkdf2.Whole.RISCV64.Fn.pbkdf2 Proof.Pbkdf2.Whole.RISCV64.Sha256.F
    verified := Proof.Pbkdf2.Whole.RISCV64.Scrub.sha256_scrubbed }]

end VG.Artifacts.Pbkdf2Sha256.RISCV64
