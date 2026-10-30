module

public import VerifiedGarbage.Proof.X448.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # X448 (RFC 7748) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.X448.Arm

def artifacts : List Artifact := [
  Spec.X448.x448Api.artifact Arm.target {
    code := Impl.X448.Arm.x448
    verified := Proof.X448.Arm.x448_verified }]

end VG.Artifacts.X448.Arm
