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

/-! # HMAC-SHA-384 (RFC 2104) on x86 -/

namespace VG.Artifacts.HmacSha384.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Hmac.sha384I.initAnyKeyApi.artifact X86.target {
    code := Impl.Hmac.X86.Fn.sha512Init Proof.Pbkdf2.Md.X86.sha384M Proof.Pbkdf2.Whole.X86.sha384F
    verified := Proof.Hmac.X86.Scrub.sha384_init_scrubbed
    spSafe := Proof.Hmac.X86.Scrub.sha384_initSp },
  Spec.Hmac.sha384I.finalizeApi.artifact X86.target {
    code := Impl.Hmac.X86.Fn.sha512Finalize Proof.Pbkdf2.Md.X86.sha384M
    verified := Proof.Hmac.X86.Scrub.sha384_fin_scrubbed
    spSafe := Proof.Hmac.X86.Scrub.sha384_finSp }]

spec_apis artifacts

end VG.Artifacts.HmacSha384.X86
