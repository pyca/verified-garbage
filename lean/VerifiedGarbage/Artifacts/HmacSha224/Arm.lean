module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeySha256
public import VerifiedGarbage.Proof.Framework.Registration

/-! # HMAC-SHA-224 (RFC 2104) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.HmacSha224.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha224I.initAnyKeyApi.artifact Arm.target {
    code := Proof.Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha224I Proof.Pbkdf2.Md.Arm.sha224Md.hmacInit Proof.Pbkdf2.Whole.Arm.sha224F
    stack := 24 + Proof.Pbkdf2.Whole.Arm.Any.anyFrame Spec.Hmac.sha224I
    verified := Proof.Pbkdf2.Whole.Arm.Any.sha224_initF },
  Spec.Hmac.sha224I.finalizeApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha224I) 1 Proof.Pbkdf2.Md.Arm.sha224Md.hmacFin
    stack := 16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha224I
    verified := Proof.Pbkdf2.Md.Arm.finFramed Proof.Pbkdf2.Md.Arm.Instances.sha224_finalize
      Proof.Hmac.sha224_local Proof.Pbkdf2.Md.Arm.sha224_finFrameSat }]

end VG.Artifacts.HmacSha224.Arm
