module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Scrub
import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # HMAC-MD5 (RFC 2104) on PPC64LE -/

namespace VG.Artifacts.HmacMd5.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Hmac.md5I.initAnyKeyApi.artifact PPC64LE.target {
    code := Impl.Hmac.Stream.PPC64LE.Fn.initMd5
    verified := Proof.Hmac.Stream.PPC64LE.Scrub.md5_init_scrubbed },
  Spec.Hmac.md5I.finalizeApi.artifact PPC64LE.target {
    code := Impl.Hmac.Stream.PPC64LE.Fn.finalizeMd5
    verified := Proof.Hmac.Stream.PPC64LE.Scrub.md5_finalize_scrubbed }]

spec_apis artifacts

end VG.Artifacts.HmacMd5.PPC64LE
