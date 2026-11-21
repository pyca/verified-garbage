module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # PBKDF2-HMAC-SHA-256 (RFC 8018) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha256.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha256I.pbkdf2Api.artifact Arm.target {
    code := Impl.Pbkdf2.Whole.Arm.Fn.sha256
    verified := Proof.Pbkdf2.Whole.Arm.Fn.sha256 }]

end VG.Artifacts.Pbkdf2Sha256.Arm
