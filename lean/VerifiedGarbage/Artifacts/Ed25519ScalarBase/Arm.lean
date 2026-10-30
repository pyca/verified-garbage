module

public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! Baseline ARMv7 Ed25519 primitive with register saves in the reviewed scratch buffer. -/

@[expose] public section

namespace VG.Artifacts.Ed25519ScalarBase.Arm

def artifacts : List Artifact := [
  Spec.Ed25519.scalarBaseApi.artifact Arm.target {
    notes := ["Uses baseline integer instructions \
      and a fixed schedule for all 256 input bits. A comb over the scalar's 64 nibbles: \
      `[17 G]B` plus, for each nibble `i`, the entry of digit `n_i - 8` of a table of \
      `[k 16^i]B` (`k = 1 … 8`, affine and cached, in the static `VG_ED25519_COMB`), selected \
      by masks from every candidate and negated for a negative digit: 64 additions of seven \
      field products and no doublings. Field products use only low 32-bit `mul` on 16-bit \
      limbs; the inversion's chain to `z^(2^250 - 1)` is a call of `vg_gf25519_r16_pow250` on \
      `scratch`. The scalar's copy, saved registers and `lr` reside in `scratch`."]
    consts := Impl.Ed25519.Arm.combConsts
    code := Impl.Ed25519.Arm.scalarBase
    verified := Proof.Ed25519.Arm.scalarBase_verified
    stack := 0 }]

end VG.Artifacts.Ed25519ScalarBase.Arm
