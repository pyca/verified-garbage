module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Proof.Hmac.Stream.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # HMAC-SHA-512/224 (RFC 2104) on ARMv7 -/

namespace VG.Artifacts.HmacSha512_224.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Hmac.sha512_224I.initAnyKeyApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.initSha512_224
    verified := Proof.Hmac.Stream.Arm.Fn.initSha512_224 },
  Spec.Hmac.sha512_224I.finalizeApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.finalizeSha512_224
    verified := Proof.Hmac.Stream.Arm.Fn.finalizeSha512_224 }]

spec_apis artifacts

end VG.Artifacts.HmacSha512_224.Arm
