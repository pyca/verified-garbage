module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeySha256
public import VerifiedGarbage.Proof.Framework.Registration

/-! # HMAC-SHA-256 (RFC 2104) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.HmacSha256.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha256I.initAnyKeyApi.artifact Arm.target {
    code := Proof.Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha256I Proof.Pbkdf2.Md.Arm.sha256Md.hmacInit Proof.Pbkdf2.Whole.Arm.sha256F
    stack := 24 + Proof.Pbkdf2.Whole.Arm.Any.anyFrame Spec.Hmac.sha256I
    verified := Proof.Pbkdf2.Whole.Arm.Any.sha256_initF },
  Spec.Hmac.sha256I.finalizeApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha256I) 1 Proof.Pbkdf2.Md.Arm.sha256Md.hmacFin
    stack := 16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha256I
    verified := Proof.Pbkdf2.Md.Arm.finFramed Proof.Pbkdf2.Md.Arm.Instances.sha256_finalize
      Proof.Hmac.sha256_local Proof.Pbkdf2.Md.Arm.sha256_finFrameSat }]

end VG.Artifacts.HmacSha256.Arm
