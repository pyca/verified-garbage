module

public import VerifiedGarbage.Proof.X25519.Arm.Verified
public import VerifiedGarbage.Proof.X25519.Arm.Base
public import VerifiedGarbage.Proof.Framework.Registration

/-! # X25519 (RFC 7748) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.X25519.Arm

def artifacts : List Artifact := [
  Spec.X25519.x25519Api.artifact Arm.target {
    notes := ["The function saves `r4`–`r11` in `scratch`. Its only \
      multiplication is `mul` (the low 32 bits of a 32 × 32-bit product): field elements are sixteen \
      16-bit limbs, multiplied row by row and reduced with `2^256 = 38` (mod p); the inversion is \
      square-and-multiply over the public bits of `p - 2`."]
    code := Impl.X25519.Arm.x25519
    verified := Proof.X25519.Arm.x25519_verified },
  Spec.X25519.x25519BaseApi.artifact Arm.target {
    notes := ["`X25519(k, 9)` is the u-coordinate \
      `(1 + y) / (1 - y)` of `[k] B` on edwards25519, `B` Ed25519's base point (RFC 7748 §4.1's \
      birational map), which the function computes with `vg_ed25519_scalar_base`'s comb rather \
      than the ladder: the scalar is copied into `scratch` and clamped there (byte 0 ANDed with \
      248, byte 31 with 127 and ORed with 64), the comb's 64 additions of entries of the static \
      `VG_ED25519_COMB` accumulate `[k] B` in extended coordinates, and `(Z + Y) / (Z - Y)` takes \
      one inversion, whose chain to `z^(2^250 - 1)` is a call of `vg_gf25519_r16_pow250`. Field \
      products use only low 32-bit `mul` on 16-bit limbs. Saved registers and `lr` reside in \
      `scratch`."]
    consts := Impl.Ed25519.Arm.combConsts
    code := Impl.X25519.Arm.Base.x25519Base
    stack := 0
    verified := Proof.X25519.Arm.Base.x25519Base_verified }]

end VG.Artifacts.X25519.Arm
