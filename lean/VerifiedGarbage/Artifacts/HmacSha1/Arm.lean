module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Proof.Hmac.Stream.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # HMAC-SHA-1 (RFC 2104) on ARMv7 -/

namespace VG.Artifacts.HmacSha1.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Hmac.sha1I.initAnyKeyApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.initSha1
    verified := Proof.Hmac.Stream.Arm.Fn.initSha1 },
  Spec.Hmac.sha1I.finalizeApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.finalizeSha1
    verified := Proof.Hmac.Stream.Arm.Fn.finalizeSha1 }]

spec_apis artifacts

end VG.Artifacts.HmacSha1.Arm
