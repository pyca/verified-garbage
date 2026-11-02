module

public import VerifiedGarbage.Proof.Argon2.RISCV64.Compress
public import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.CT
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Argon2 (RFC 9106) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Argon2.RISCV64

def artifacts : List Artifact := [
  Spec.Argon2.deriveApi.artifact RISCV64.target {
    code := Impl.Argon2.RISCV64.Derive.derive
    stack := 320
    verified := Proof.Argon2.RISCV64.Derive.deriveShared_verified }]

end VG.Artifacts.Argon2.RISCV64
