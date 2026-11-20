module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # PBKDF2-HMAC-MD5 (RFC 8018) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Md5.Arm

def artifacts : List Artifact := [
  Spec.Hmac.md5I.pbkdf2Api.artifact Arm.target {
    code := Impl.Pbkdf2.Whole.Arm.Fn.md5
    verified := .scrubbed Proof.Pbkdf2.Whole.Arm.Fn.md5 }]

end VG.Artifacts.Pbkdf2Md5.Arm
