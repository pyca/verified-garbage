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

/-! # HMAC-SHA-512/224 (RFC 2104) on x86 -/

namespace VG.Artifacts.HmacSha512_224.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Hmac.sha512_224I.initAnyKeyApi.artifact X86.target {
    code := Impl.Hmac.X86.Fn.sha512Init Proof.Pbkdf2.Md.X86.sha512_224M Proof.Pbkdf2.Whole.X86.sha512_224F
    verified := Proof.Hmac.X86.Scrub.sha512_224_init_scrubbed
    spSafe := Proof.Hmac.X86.Scrub.sha512_224_initSp },
  Spec.Hmac.sha512_224I.finalizeApi.artifact X86.target {
    code := Impl.Hmac.X86.Fn.sha512Finalize Proof.Pbkdf2.Md.X86.sha512_224M
    verified := Proof.Hmac.X86.Scrub.sha512_224_fin_scrubbed
    spSafe := Proof.Hmac.X86.Scrub.sha512_224_finSp }]

spec_apis artifacts

end VG.Artifacts.HmacSha512_224.X86
