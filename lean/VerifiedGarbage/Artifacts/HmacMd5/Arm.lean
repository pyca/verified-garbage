module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeyInstances
public import VerifiedGarbage.Proof.Framework.Registration

/-! # HMAC-MD5 (RFC 2104) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.HmacMd5.Arm

def artifacts : List Artifact := [
  Spec.Hmac.md5I.initAnyKeyApi.artifact Arm.target {
    code := Proof.Pbkdf2.Whole.Arm.initCode Spec.Hmac.md5I Proof.Pbkdf2.Md.Arm.md5Md.hmacInit Proof.Pbkdf2.Whole.Arm.md5F
    stack := 24 + Proof.Pbkdf2.Whole.Arm.Any.anyFrame Spec.Hmac.md5I
    verified := Proof.Pbkdf2.Whole.Arm.Any.md5_initF },
  Spec.Hmac.md5I.finalizeApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.md5I) 1 Proof.Pbkdf2.Md.Arm.md5Md.hmacFin
    stack := 16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.md5I
    verified := Proof.Pbkdf2.Md.Arm.finFramed Proof.Pbkdf2.Md.Arm.Instances.md5_finalize
      Proof.Hmac.md5_local Proof.Pbkdf2.Md.Arm.md5_finFrameSat }]

end VG.Artifacts.HmacMd5.Arm
