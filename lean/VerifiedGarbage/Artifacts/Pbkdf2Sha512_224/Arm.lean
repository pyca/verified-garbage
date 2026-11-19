module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # PBKDF2-HMAC-SHA-512/224 (RFC 8018) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha512_224.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha512_224I.pbkdf2Api.artifact Arm.target Proof.Pbkdf2.Whole.Arm.Scrub.sha512_224RegArm]

end VG.Artifacts.Pbkdf2Sha512_224.Arm
