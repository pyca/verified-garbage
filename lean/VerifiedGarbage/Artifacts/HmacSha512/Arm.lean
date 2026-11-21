module

public import VerifiedGarbage.Proof.Hmac.Stream.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # HMAC-SHA-512 (RFC 2104) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.HmacSha512.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha512I.initAnyKeyApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.initSha512
    verified := Proof.Hmac.Stream.Arm.Fn.initSha512 },
  Spec.Hmac.sha512I.finalizeApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.finalizeSha512
    verified := Proof.Hmac.Stream.Arm.Fn.finalizeSha512 }]

end VG.Artifacts.HmacSha512.Arm
