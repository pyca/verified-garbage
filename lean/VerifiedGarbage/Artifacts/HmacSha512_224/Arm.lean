module

public import VerifiedGarbage.Proof.Hmac.Stream.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # HMAC-SHA-512/224 (RFC 2104) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.HmacSha512_224.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha512_224I.initAnyKeyApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.initSha512_224
    verified := Proof.Hmac.Stream.Arm.Fn.initSha512_224 },
  Spec.Hmac.sha512_224I.finalizeApi.artifact Arm.target {
    code := Impl.Hmac.Stream.Arm.Fn.finalizeSha512_224
    verified := Proof.Hmac.Stream.Arm.Fn.finalizeSha512_224 }]

end VG.Artifacts.HmacSha512_224.Arm
