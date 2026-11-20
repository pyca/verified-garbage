module

public import VerifiedGarbage.Proof.Hmac.X86.Scrub
public import VerifiedGarbage.Impl.Hmac.X86
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Hashes
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Lit
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Lit

/-! # HMAC-SHA-512/256 (RFC 2104) on x86 -/

@[expose] public section

namespace VG.Artifacts.HmacSha512_256.X86

def artifacts : List Artifact := [
  Spec.Hmac.sha512_256I.initAnyKeyApi.artifact X86.target {
    code := Impl.Hmac.X86.Fn.sha512Init Proof.Pbkdf2.Md.X86.sha512_256M Proof.Pbkdf2.Whole.X86.sha512_256F
    verified := .scrubbed Proof.Hmac.X86.Scrub.sha512_256_init_scrubbed
    spSafe := Proof.Hmac.X86.Scrub.sha512_256_initSp },
  Spec.Hmac.sha512_256I.finalizeApi.artifact X86.target {
    code := Impl.Hmac.X86.Fn.sha512Finalize Proof.Pbkdf2.Md.X86.sha512_256M
    verified := .scrubbed Proof.Hmac.X86.Scrub.sha512_256_fin_scrubbed
    spSafe := Proof.Hmac.X86.Scrub.sha512_256_finSp }]

end VG.Artifacts.HmacSha512_256.X86
