module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.P384.PPC64LE
public import VerifiedGarbage.Proof.EcKey.PPC64LE.P384.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P384
import VerifiedGarbage.Proof.EcKey.PPC64LE.P384.Lit

/-!
# P-384 public keys (FIPS 186-5 §A.2) on PPC64LE

A generic file (see `TCB/Emit.lean`) over P-384's group law `h`, the variant
`Variants/P384/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P384.PPC64LE.EcP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.EcKey.P384.publicKeyApi.artifact PPC64LE.target {
    notes := ["The function is `vg_ecdsa_p384_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it \
      saves `r14`, `r31` and `lr` in `scratch` (in `r3` during the function), and keeps `out` in \
      `r14`; field elements are six 64-bit words in Montgomery form, multiplied by \
      word-by-word Montgomery multiplication (CIOS, in calls of `vg_p384_mul_mod_p` and the other \
      functions of `p384_mont`) with a final conditional subtraction; `[d]G` is a double-and-add \
      ladder over all 384 bits of `d`, with the complete addition formulas of Renes, Costello and \
      Batina for every addition and doubling (calls of `vg_p384_point_double` and \
      `vg_p384_point_add`) and a masked selection for each bit; and `Z⁻¹` is Fermat's, \
      by square-and-always-multiply over the bits of `p - 2`. The result (or zeros) is selected \
      by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."]
    code := Impl.EcKey.PPC64LE.publicKeyP384
    verified := Proof.EcKey.PPC64LE.P384.pk_verified h.law }]

end VG.Generic.P384.PPC64LE.EcP384
