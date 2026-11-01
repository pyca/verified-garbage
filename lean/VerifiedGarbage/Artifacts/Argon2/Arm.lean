module

public import VerifiedGarbage.Proof.Argon2.Arm.Derive.Verified
public import VerifiedGarbage.Proof.Argon2.Arm.CompressVerified
public import VerifiedGarbage.Proof.Argon2.Arm.HPrime.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Argon2 (RFC 9106) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Argon2.Arm

def artifacts : List Artifact := [
  Spec.Argon2.deriveApi.artifact Arm.target {
    code := Impl.Argon2.Arm.Derive.derive
    stack := 240
    verified := Proof.Argon2.Arm.Derive.deriveShared_verified }]

end VG.Artifacts.Argon2.Arm
