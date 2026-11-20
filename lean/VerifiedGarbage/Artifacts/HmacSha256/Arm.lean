module

public import VerifiedGarbage.Proof.Hmac.Stream.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # HMAC-SHA-256 (RFC 2104) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.HmacSha256.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha256I.initAnyKeyApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.initSha256
    verified := .scrubbed Proof.Hmac.Stream.Arm.Fn.initSha256 },
  Spec.Hmac.sha256I.finalizeApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.finalizeSha256
    verified := .scrubbed Proof.Hmac.Stream.Arm.Fn.finalizeSha256 }]

end VG.Artifacts.HmacSha256.Arm
