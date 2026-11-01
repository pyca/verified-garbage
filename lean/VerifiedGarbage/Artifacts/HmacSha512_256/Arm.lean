module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeyInstances
public import VerifiedGarbage.Proof.Framework.Registration

/-! # HMAC-SHA-512/256 (RFC 2104) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.HmacSha512_256.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha512_256I.initAnyKeyApi.artifact Arm.target {
    code := Proof.Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha512_256I Proof.Pbkdf2.Md.Arm.sha512_256Md.hmacInit Proof.Pbkdf2.Whole.Arm.sha512_256F
    stack := 24 + Proof.Pbkdf2.Whole.Arm.Any.anyFrame Spec.Hmac.sha512_256I
    verified := Proof.Pbkdf2.Whole.Arm.Any.sha512_256_initF },
  Spec.Hmac.sha512_256I.finalizeApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha512_256I) 1 Proof.Pbkdf2.Md.Arm.sha512_256Md.hmacFin
    stack := 16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha512_256I
    verified := Proof.Pbkdf2.Md.Arm.finFramed Proof.Pbkdf2.Md.Arm.Instances.sha512_256_finalize
      Proof.Hmac.sha512_256_local Proof.Pbkdf2.Md.Arm.sha512_256_finFrameSat }]

end VG.Artifacts.HmacSha512_256.Arm
