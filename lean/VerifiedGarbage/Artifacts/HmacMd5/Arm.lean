module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Proof.Hmac.Stream.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # HMAC-MD5 (RFC 2104) on ARMv7 -/

namespace VG.Artifacts.HmacMd5.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Hmac.md5I.initAnyKeyApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.initMd5
    verified := Proof.Hmac.Stream.Arm.Fn.initMd5 },
  Spec.Hmac.md5I.finalizeApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.finalizeMd5
    verified := Proof.Hmac.Stream.Arm.Fn.finalizeMd5 }]

spec_apis artifacts

end VG.Artifacts.HmacMd5.Arm
