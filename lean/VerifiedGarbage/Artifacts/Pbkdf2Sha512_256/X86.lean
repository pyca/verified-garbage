module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Scrub
public import VerifiedGarbage.Impl.Pbkdf2.Whole.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Lit
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.X86.Print

/-! # PBKDF2-HMAC-SHA-512/256 (RFC 8018) on x86 -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha512_256.X86

def artifacts : List Artifact := [
  Spec.Hmac.sha512_256I.pbkdf2Api.artifact X86.target {
    code := Impl.Pbkdf2.Whole.X86.Fn.sha512 Proof.Pbkdf2.Whole.X86.sha512_256F
    verified := .scrubbed Proof.Pbkdf2.Whole.X86.Scrub.sha512_256_scrubbed }]

end VG.Artifacts.Pbkdf2Sha512_256.X86
