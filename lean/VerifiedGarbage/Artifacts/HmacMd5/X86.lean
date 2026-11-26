module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Proof.Hmac.X86.Scrub
import VerifiedGarbage.Impl.Hmac.X86
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Hashes
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Lit
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # HMAC-MD5 (RFC 2104) on x86 -/

namespace VG.Artifacts.HmacMd5.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Hmac.md5I.initAnyKeyApi.artifact X86.target {
    code := Impl.Hmac.X86.Fn.md5Init Proof.Pbkdf2.Md.X86.md5M Proof.Pbkdf2.Whole.X86.md5F
    verified := Proof.Hmac.X86.Scrub.md5_init_scrubbed
    spSafe := Proof.Hmac.X86.Scrub.md5_initSp },
  Spec.Hmac.md5I.finalizeApi.artifact X86.target {
    code := Impl.Hmac.X86.Fn.md5Finalize Proof.Pbkdf2.Md.X86.md5M
    verified := Proof.Hmac.X86.Scrub.md5_fin_scrubbed
    spSafe := Proof.Hmac.X86.Scrub.md5_finSp }]

spec_apis artifacts

end VG.Artifacts.HmacMd5.X86
