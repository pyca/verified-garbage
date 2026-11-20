module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Scrub
public import VerifiedGarbage.Impl.Pbkdf2.Whole.RISCV64.Fn
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # PBKDF2-HMAC-MD5 (RFC 8018) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Md5.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.md5I.pbkdf2Api.artifact RISCV64.target {
    code := Impl.Pbkdf2.Whole.RISCV64.Fn.pbkdf2 Proof.Pbkdf2.Whole.RISCV64.Md5.F
    verified := .scrubbed Proof.Pbkdf2.Whole.RISCV64.Scrub.md5_scrubbed }]

end VG.Artifacts.Pbkdf2Md5.RISCV64
