module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Sha224
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # PBKDF2-HMAC-SHA-224 (RFC 8018) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha224.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.sha224I.pbkdf2Api.artifact RISCV64.target {
    code := Proof.Pbkdf2.Whole.RISCV64.Sha224.F.pbkdf2
    verified := Proof.Pbkdf2.Whole.RISCV64.Sha224.pbkdf2 }]

end VG.Artifacts.Pbkdf2Sha224.RISCV64
