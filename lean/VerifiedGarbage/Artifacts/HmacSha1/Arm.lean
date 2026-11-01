module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeyInstances
public import VerifiedGarbage.Proof.Framework.Registration

/-! # HMAC-SHA-1 (RFC 2104) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.HmacSha1.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha1I.initAnyKeyApi.artifact Arm.target {
    code := Proof.Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha1I Proof.Pbkdf2.Md.Arm.sha1Md.hmacInit Proof.Pbkdf2.Whole.Arm.sha1F
    stack := 24 + Proof.Pbkdf2.Whole.Arm.Any.anyFrame Spec.Hmac.sha1I
    verified := Proof.Pbkdf2.Whole.Arm.Any.sha1_initF },
  Spec.Hmac.sha1I.finalizeApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha1I) 1 Proof.Pbkdf2.Md.Arm.sha1Md.hmacFin
    stack := 16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha1I
    verified := Proof.Pbkdf2.Md.Arm.finFramed Proof.Pbkdf2.Md.Arm.Instances.sha1_finalize
      Proof.Hmac.sha1_local Proof.Pbkdf2.Md.Arm.sha1_finFrameSat }]

end VG.Artifacts.HmacSha1.Arm
