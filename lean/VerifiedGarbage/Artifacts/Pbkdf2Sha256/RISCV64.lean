module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Sha256
public import VerifiedGarbage.Proof.Framework.Registration

/-! # PBKDF2-HMAC-SHA-256 (RFC 8018) on RISC-V: the iteration and the whole derivation -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha256.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.sha256I.pbkdf2Api.artifact RISCV64.target {
    code := Proof.Pbkdf2.Whole.RISCV64.Sha256.F.pbkdf2
    stack := Proof.Pbkdf2.Whole.RISCV64.Sha256.F.itB + Proof.Pbkdf2.Whole.RISCV64.Sha256.F.frB +
      Proof.Pbkdf2.Whole.RISCV64.Sha256.F.X
    verified := Proof.Pbkdf2.Whole.RISCV64.Sha256.pbkdf2 }]

end VG.Artifacts.Pbkdf2Sha256.RISCV64
