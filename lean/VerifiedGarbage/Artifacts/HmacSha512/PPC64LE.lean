module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Scrub
import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # HMAC-SHA-512 (RFC 2104) on PPC64LE -/

namespace VG.Artifacts.HmacSha512.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Hmac.sha512I.initAnyKeyApi.artifact PPC64LE.target {
    code := Impl.Hmac.Stream.PPC64LE.Fn.initSha512
    verified := Proof.Hmac.Stream.PPC64LE.Scrub.sha512_init_scrubbed },
  Spec.Hmac.sha512I.finalizeApi.artifact PPC64LE.target {
    code := Impl.Hmac.Stream.PPC64LE.Fn.finalizeSha512
    verified := Proof.Hmac.Stream.PPC64LE.Scrub.sha512_finalize_scrubbed }]

spec_apis artifacts

end VG.Artifacts.HmacSha512.PPC64LE
