module

public import VerifiedGarbage.Proof.Hmac.Stream.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # HMAC-MD5 (RFC 2104) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.HmacMd5.Arm

def artifacts : List Artifact := [
  Spec.Hmac.md5I.initAnyKeyApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.initMd5
    verified := .scrubbed Proof.Hmac.Stream.Arm.Fn.initMd5 },
  Spec.Hmac.md5I.finalizeApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.finalizeMd5
    verified := .scrubbed Proof.Hmac.Stream.Arm.Fn.finalizeMd5 }]

end VG.Artifacts.HmacMd5.Arm
