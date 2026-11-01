module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeyInstances
public import VerifiedGarbage.Proof.Framework.Registration

/-! # HMAC-SHA-512 (RFC 2104) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.HmacSha512.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha512I.initAnyKeyApi.artifact Arm.target {
    code := Proof.Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha512I Proof.Pbkdf2.Md.Arm.sha512Md'.hmacInit Proof.Pbkdf2.Whole.Arm.sha512F
    stack := 24 + Proof.Pbkdf2.Whole.Arm.Any.anyFrame Spec.Hmac.sha512I
    verified := Proof.Pbkdf2.Whole.Arm.Any.sha512_initF },
  Spec.Hmac.sha512I.finalizeApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha512I) 1 Proof.Pbkdf2.Md.Arm.sha512Md'.hmacFin
    stack := 16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha512I
    verified := Proof.Pbkdf2.Md.Arm.finFramed Proof.Pbkdf2.Md.Arm.Instances.sha512_finalize
      Proof.Hmac.sha512_local Proof.Pbkdf2.Md.Arm.sha512_finFrameSat }]

end VG.Artifacts.HmacSha512.Arm
