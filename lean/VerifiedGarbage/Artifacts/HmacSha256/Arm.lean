module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Proof.Hmac.Stream.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # HMAC-SHA-256 (RFC 2104) on ARMv7 -/

namespace VG.Artifacts.HmacSha256.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Hmac.sha256I.initAnyKeyApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.initSha256
    verified := Proof.Hmac.Stream.Arm.Fn.initSha256 },
  Spec.Hmac.sha256I.finalizeApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.finalizeSha256
    verified := Proof.Hmac.Stream.Arm.Fn.finalizeSha256 }]

spec_apis artifacts

end VG.Artifacts.HmacSha256.Arm
