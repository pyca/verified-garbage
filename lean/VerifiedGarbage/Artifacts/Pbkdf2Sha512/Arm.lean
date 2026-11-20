module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # PBKDF2-HMAC-SHA-512 (RFC 8018) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha512.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha512I.pbkdf2Api.artifact Arm.target {
    code := Impl.Pbkdf2.Whole.Arm.Fn.sha512
    verified := .scrubbed Proof.Pbkdf2.Whole.Arm.Fn.sha512 }]

end VG.Artifacts.Pbkdf2Sha512.Arm
