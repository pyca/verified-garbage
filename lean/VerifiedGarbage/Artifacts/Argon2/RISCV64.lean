module

public import VerifiedGarbage.Proof.Argon2.RISCV64.Compress
public import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.CT
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Argon2.RISCV64.Scrub
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Impl.Argon2.RISCV64.Fn

/-! # Argon2 (RFC 9106) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Argon2.RISCV64

def artifacts : List (Artifact RISCV64.target) := [
  Spec.Argon2.deriveApi.artifact RISCV64.target {
    code := Impl.Argon2.RISCV64.Fn.derive
    verified := Proof.Argon2.RISCV64.Scrub.derive_scrubbed }]

end VG.Artifacts.Argon2.RISCV64
