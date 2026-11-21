module

public import VerifiedGarbage.Proof.Hmac.Stream.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # HMAC-SHA-224 (RFC 2104) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.HmacSha224.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha224I.initAnyKeyApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.initSha224
    verified := Proof.Hmac.Stream.Arm.Fn.initSha224 },
  Spec.Hmac.sha224I.finalizeApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.finalizeSha224
    verified := Proof.Hmac.Stream.Arm.Fn.finalizeSha224 }]

end VG.Artifacts.HmacSha224.Arm
