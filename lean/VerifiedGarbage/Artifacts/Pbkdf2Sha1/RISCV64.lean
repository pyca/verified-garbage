module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Scrub
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # PBKDF2-HMAC-SHA-1 (RFC 8018) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha1.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.sha1I.pbkdf2Api.artifact RISCV64.target Proof.Pbkdf2.Whole.RISCV64.Scrub.sha1Pbkdf2Reg]

end VG.Artifacts.Pbkdf2Sha1.RISCV64
