module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Scrub
public import VerifiedGarbage.Impl.Pbkdf2.Whole.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Lit
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.X86.Print

/-! # PBKDF2-HMAC-SHA-384 (RFC 8018) on x86 -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha384.X86

def artifacts : List Artifact := [
  Spec.Hmac.sha384I.pbkdf2Api.artifact X86.target {
    code := Impl.Pbkdf2.Whole.X86.Fn.sha512 Proof.Pbkdf2.Whole.X86.sha384F
    verified := Proof.Pbkdf2.Whole.X86.Scrub.sha384_scrubbed }]

end VG.Artifacts.Pbkdf2Sha384.X86
