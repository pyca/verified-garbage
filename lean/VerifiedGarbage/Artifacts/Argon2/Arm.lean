module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Argon2 (RFC 9106) on ARMv7 -/

namespace VG.Artifacts.Argon2.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Argon2.deriveApi.artifact Arm.target {
    code := Impl.Argon2.Arm.Fn.derive
    verified := Proof.Argon2.Arm.Fn.derive }]

spec_apis artifacts

end VG.Artifacts.Argon2.Arm
