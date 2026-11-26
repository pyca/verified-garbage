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

/-! # PBKDF2-HMAC-MD5 (RFC 8018) on x86 -/

namespace VG.Artifacts.Pbkdf2Md5.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Hmac.md5I.pbkdf2Api.artifact X86.target {
    code := Impl.Pbkdf2.Whole.X86.Fn.md5 Proof.Pbkdf2.Whole.X86.md5F
    verified := Proof.Pbkdf2.Whole.X86.Scrub.md5_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Pbkdf2Md5.X86
