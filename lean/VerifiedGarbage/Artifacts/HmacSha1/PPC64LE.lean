module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Scrub
import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # HMAC-SHA-1 (RFC 2104) on PPC64LE -/

namespace VG.Artifacts.HmacSha1.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Hmac.sha1I.initAnyKeyApi.artifact PPC64LE.target {
    code := Impl.Hmac.Stream.PPC64LE.Fn.initSha1
    verified := Proof.Hmac.Stream.PPC64LE.Scrub.sha1_init_scrubbed },
  Spec.Hmac.sha1I.finalizeApi.artifact PPC64LE.target {
    code := Impl.Hmac.Stream.PPC64LE.Fn.finalizeSha1
    verified := Proof.Hmac.Stream.PPC64LE.Scrub.sha1_finalize_scrubbed }]

spec_apis artifacts

end VG.Artifacts.HmacSha1.PPC64LE
