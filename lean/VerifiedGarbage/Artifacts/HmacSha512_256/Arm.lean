module

public import VerifiedGarbage.Proof.Hmac.Stream.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # HMAC-SHA-512/256 (RFC 2104) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.HmacSha512_256.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha512_256I.initAnyKeyApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.initSha512_256
    verified := .scrubbed Proof.Hmac.Stream.Arm.Fn.initSha512_256 },
  Spec.Hmac.sha512_256I.finalizeApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.finalizeSha512_256
    verified := .scrubbed Proof.Hmac.Stream.Arm.Fn.finalizeSha512_256 }]

end VG.Artifacts.HmacSha512_256.Arm
