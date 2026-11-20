module

public import VerifiedGarbage.Proof.Hmac.Stream.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # HMAC-SHA-1 (RFC 2104) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.HmacSha1.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha1I.initAnyKeyApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.initSha1
    verified := .scrubbed Proof.Hmac.Stream.Arm.Fn.initSha1 },
  Spec.Hmac.sha1I.finalizeApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.finalizeSha1
    verified := .scrubbed Proof.Hmac.Stream.Arm.Fn.finalizeSha1 }]

end VG.Artifacts.HmacSha1.Arm
