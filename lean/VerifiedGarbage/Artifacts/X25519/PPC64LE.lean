module

public import VerifiedGarbage.Proof.X25519.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # X25519 (RFC 7748) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.X25519.PPC64LE

def artifacts : List Artifact := [
  Spec.X25519.x25519Api.artifact PPC64LE.target {
    notes := ["The function uses only volatile registers. Field elements are eight 32-bit limbs, one to a word of `scratch`, multiplied row \
      by row with `mulld` (each step `a_i b_j + acc + carry` fits in 64 bits) and reduced with \
      `2^256 = 38` (mod p); the inversion is square-and-multiply over the public bits of `p - 2`."]
    code := Impl.X25519.PPC64LE.x25519
    verified := Proof.X25519.PPC64LE.x25519_verified }]

end VG.Artifacts.X25519.PPC64LE
