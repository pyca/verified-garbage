module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Scrub
import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # PBKDF2-HMAC-SHA-384 (RFC 8018) on PPC64LE -/

namespace VG.Artifacts.Pbkdf2Sha384.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Hmac.sha384I.pbkdf2Api.artifact PPC64LE.target {
    code := Impl.Pbkdf2.Whole.PPC64LE.Fn.sha384
    verified := Proof.Pbkdf2.Whole.PPC64LE.Scrub.sha384_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Pbkdf2Sha384.PPC64LE
