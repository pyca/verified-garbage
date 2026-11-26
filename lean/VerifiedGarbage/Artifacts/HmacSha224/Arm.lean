module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Proof.Hmac.Stream.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # HMAC-SHA-224 (RFC 2104) on ARMv7 -/

namespace VG.Artifacts.HmacSha224.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Hmac.sha224I.initAnyKeyApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.initSha224
    verified := Proof.Hmac.Stream.Arm.Fn.initSha224 },
  Spec.Hmac.sha224I.finalizeApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.finalizeSha224
    verified := Proof.Hmac.Stream.Arm.Fn.finalizeSha224 }]

spec_apis artifacts

end VG.Artifacts.HmacSha224.Arm
