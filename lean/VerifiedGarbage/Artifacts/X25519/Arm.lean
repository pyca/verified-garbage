module

public import VerifiedGarbage.Proof.X25519.Arm.Verified
public import VerifiedGarbage.Proof.X25519.Arm.Base
public import VerifiedGarbage.Proof.Framework.Registration

/-! # X25519 (RFC 7748) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.X25519.Arm

def artifacts : List Artifact := [
  Spec.X25519.x25519Api.artifact Arm.target {
    code := Impl.X25519.Arm.x25519
    verified := Proof.X25519.Arm.x25519_verified },
  Spec.X25519.x25519Api.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.X25519.Arm.x25519Umaal
    verified := Proof.X25519.Arm.x25519Umaal_verified
    features := ["umaal"] },
  Spec.X25519.x25519BaseApi.artifact Arm.target {
    consts := Impl.Ed25519.Arm.combConsts
    code := Impl.X25519.Arm.Base.x25519Base
    stack := 0
    verified := Proof.X25519.Arm.Base.x25519Base_verified }]

end VG.Artifacts.X25519.Arm
