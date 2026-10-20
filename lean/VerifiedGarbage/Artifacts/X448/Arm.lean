module

public import VerifiedGarbage.Proof.X448.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # X448 (RFC 7748) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.X448.Arm

def artifacts : List Artifact := [
  Spec.X448.x448Api.artifact Arm.target {
    notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements are twenty-eight 16-bit limbs; multiplications, \
      additions, subtractions and the multiplication by a24 are calls of the `vg_gf448_r16_*` \
      functions on `scratch`. Inversion uses an addition chain for `p - 2`."]
    code := Impl.X448.Arm.x448
    verified := Proof.X448.Arm.x448_verified }]

end VG.Artifacts.X448.Arm
