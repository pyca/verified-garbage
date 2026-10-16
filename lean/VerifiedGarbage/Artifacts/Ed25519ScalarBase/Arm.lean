module

public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! Baseline ARMv7 Ed25519 primitive with register saves in the reviewed scratch buffer. -/

@[expose] public section

namespace VG.Artifacts.Ed25519ScalarBase.Arm

def artifacts : List Artifact := [
  Spec.Ed25519.scalarBaseApi.artifact Arm.target {
    notes := ["Uses baseline integer instructions \
      and a fixed schedule for all 256 input bits. Field products use only low 32-bit \
      `mul` on 16-bit limbs. Point additions and doublings are calls of \
      `vg_ed25519_r16_point_add` and `vg_ed25519_r16_point_double`, and the inversion's chain to \
      `z^(2^250 - 1)` a call of `vg_gf25519_r16_pow250`, each on `scratch`. Point tables, saved \
      registers and `lr` reside in `scratch`."]
    code := Impl.Ed25519.Arm.scalarBase
    verified := Proof.Ed25519.Arm.scalarBase_verified
    stack := 0 }]

end VG.Artifacts.Ed25519ScalarBase.Arm
