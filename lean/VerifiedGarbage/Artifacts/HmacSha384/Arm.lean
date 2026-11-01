module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeyInstances
public import VerifiedGarbage.Proof.Framework.Registration

/-! # HMAC-SHA-384 (RFC 2104) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.HmacSha384.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha384I.initAnyKeyApi.artifact Arm.target {
    code := Proof.Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha384I Proof.Pbkdf2.Md.Arm.sha384Md.hmacInit Proof.Pbkdf2.Whole.Arm.sha384F
    stack := 24 + Proof.Pbkdf2.Whole.Arm.Any.anyFrame Spec.Hmac.sha384I
    verified := Proof.Pbkdf2.Whole.Arm.Any.sha384_initF },
  Spec.Hmac.sha384I.finalizeApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha384I) 1 Proof.Pbkdf2.Md.Arm.sha384Md.hmacFin
    stack := 16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha384I
    verified := Proof.Pbkdf2.Md.Arm.finFramed Proof.Pbkdf2.Md.Arm.Instances.sha384_finalize
      Proof.Hmac.sha384_local Proof.Pbkdf2.Md.Arm.sha384_finFrameSat }]

end VG.Artifacts.HmacSha384.Arm
