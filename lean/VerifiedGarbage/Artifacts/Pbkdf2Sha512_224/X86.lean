module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Scrub
import VerifiedGarbage.Impl.Pbkdf2.Whole.X86.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # PBKDF2-HMAC-SHA-512/224 (RFC 8018) on x86 -/

namespace VG.Artifacts.Pbkdf2Sha512_224.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Hmac.sha512_224I.pbkdf2Api.artifact X86.target {
    code := Impl.Pbkdf2.Whole.X86.Fn.sha512 Proof.Pbkdf2.Whole.X86.sha512_224F
    verified := Proof.Pbkdf2.Whole.X86.Scrub.sha512_224_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Pbkdf2Sha512_224.X86
