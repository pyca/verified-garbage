module

public import VerifiedGarbage.Proof.Argon2.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Argon2 (RFC 9106) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Argon2.Arm

def artifacts : List Artifact := [
  Spec.Argon2.deriveApi.artifact Arm.target {
    code := Impl.Argon2.Arm.Fn.derive
    verified := Proof.Argon2.Arm.Fn.derive }]

end VG.Artifacts.Argon2.Arm
