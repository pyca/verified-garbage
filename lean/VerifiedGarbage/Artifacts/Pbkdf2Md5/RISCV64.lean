module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Md5
public import VerifiedGarbage.Proof.Framework.Registration

/-! # PBKDF2-HMAC-MD5 (RFC 8018) on RISC-V: the iteration and the whole derivation -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Md5.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.md5I.pbkdf2Api.artifact RISCV64.target {
    code := Proof.Pbkdf2.Whole.RISCV64.Md5.F.pbkdf2
    stack := Proof.Pbkdf2.Whole.RISCV64.Md5.F.itB + Proof.Pbkdf2.Whole.RISCV64.Md5.F.frB +
      Proof.Pbkdf2.Whole.RISCV64.Md5.F.X
    verified := Proof.Pbkdf2.Whole.RISCV64.Md5.pbkdf2 }]

end VG.Artifacts.Pbkdf2Md5.RISCV64
