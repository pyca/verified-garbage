module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # PBKDF2-HMAC-SHA-224 (RFC 8018) on ARMv7 -/

namespace VG.Artifacts.Pbkdf2Sha224.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Hmac.sha224I.pbkdf2Api.artifact Arm.target {
    code := Impl.Pbkdf2.Whole.Arm.Fn.sha224
    verified := Proof.Pbkdf2.Whole.Arm.Fn.sha224 }]

spec_apis artifacts

end VG.Artifacts.Pbkdf2Sha224.Arm
