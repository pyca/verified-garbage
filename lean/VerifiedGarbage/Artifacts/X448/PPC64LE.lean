module

public import VerifiedGarbage.Proof.X448.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # X448 (RFC 7748) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.X448.PPC64LE

def artifacts : List Artifact := [
  Spec.X448.x448Api.artifact PPC64LE.target {
    notes := ["The function uses only volatile registers. Field elements are fourteen 32-bit limbs, one to a word of `scratch`, multiplied row \
      by row with `mulld` (each step `a_i b_j + acc + carry` fits in 64 bits) and reduced with \
      `2^448 = 2^224 + 1` (mod p); the inversion is square-and-multiply over the public bits of \
      `p - 2`."]
    code := Impl.X448.PPC64LE.x448
    verified := Proof.X448.PPC64LE.x448_verified }]

end VG.Artifacts.X448.PPC64LE
