module

public import VerifiedGarbage.Proof.Hmac.X86.Scrub
public import VerifiedGarbage.Impl.Hmac.X86
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Hashes
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Lit
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Lit

/-! # HMAC-SHA-512 (RFC 2104) on x86 -/

@[expose] public section

namespace VG.Artifacts.HmacSha512.X86

def artifacts : List Artifact := [
  Spec.Hmac.sha512I.initAnyKeyApi.artifact X86.target {
    code := Impl.Hmac.X86.Fn.sha512Init Proof.Pbkdf2.Md.X86.sha512M' Proof.Pbkdf2.Whole.X86.sha512F
    verified := Proof.Hmac.X86.Scrub.sha512_init_scrubbed
    spSafe := Proof.Hmac.X86.Scrub.sha512_initSp },
  Spec.Hmac.sha512I.finalizeApi.artifact X86.target {
    code := Impl.Hmac.X86.Fn.sha512Finalize Proof.Pbkdf2.Md.X86.sha512M'
    verified := Proof.Hmac.X86.Scrub.sha512_fin_scrubbed
    spSafe := Proof.Hmac.X86.Scrub.sha512_finSp }]

end VG.Artifacts.HmacSha512.X86
