module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Sha512_256
public import VerifiedGarbage.Proof.Framework.Registration

/-! # PBKDF2-HMAC-SHA-512/256 (RFC 8018) on RISC-V: the iteration and the whole derivation -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha512_256.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.sha512_256I.pbkdf2Api.artifact RISCV64.target {
    code := Proof.Pbkdf2.Whole.RISCV64.Sha512_256.F.pbkdf2
    stack := Proof.Pbkdf2.Whole.RISCV64.Sha512_256.F.itB + Proof.Pbkdf2.Whole.RISCV64.Sha512_256.F.frB +
      Proof.Pbkdf2.Whole.RISCV64.Sha512_256.F.X
    verified := Proof.Pbkdf2.Whole.RISCV64.Sha512_256.pbkdf2 }]

end VG.Artifacts.Pbkdf2Sha512_256.RISCV64
