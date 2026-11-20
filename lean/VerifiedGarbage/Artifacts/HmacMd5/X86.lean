module

public import VerifiedGarbage.Proof.Hmac.X86.Scrub
public import VerifiedGarbage.Impl.Hmac.X86
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Hashes
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Lit
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Lit

/-! # HMAC-MD5 (RFC 2104) on x86 -/

@[expose] public section

namespace VG.Artifacts.HmacMd5.X86

def artifacts : List Artifact := [
  Spec.Hmac.md5I.initAnyKeyApi.artifact X86.target {
    code := Impl.Hmac.X86.Fn.md5Init Proof.Pbkdf2.Md.X86.md5M Proof.Pbkdf2.Whole.X86.md5F
    verified := .scrubbed Proof.Hmac.X86.Scrub.md5_init_scrubbed
    spSafe := Proof.Hmac.X86.Scrub.md5_initSp },
  Spec.Hmac.md5I.finalizeApi.artifact X86.target {
    code := Impl.Hmac.X86.Fn.md5Finalize Proof.Pbkdf2.Md.X86.md5M
    verified := .scrubbed Proof.Hmac.X86.Scrub.md5_fin_scrubbed
    spSafe := Proof.Hmac.X86.Scrub.md5_finSp }]

end VG.Artifacts.HmacMd5.X86
