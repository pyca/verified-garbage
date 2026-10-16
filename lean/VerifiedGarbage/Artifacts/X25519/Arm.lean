module

public import VerifiedGarbage.Proof.X25519.Arm.Verified
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
    verified := Proof.X25519.Arm.x25519_verified }]

end VG.Artifacts.X25519.Arm
