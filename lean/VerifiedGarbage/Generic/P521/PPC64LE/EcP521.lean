module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.P521.PPC64LE
public import VerifiedGarbage.Proof.EcKey.PPC64LE.P521.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P521
import VerifiedGarbage.Proof.EcKey.PPC64LE.P521.Lit

/-!
# P-521 public keys (FIPS 186-5 §A.2) on PPC64LE

A generic file (see `TCB/Emit.lean`) over P-521's group law `h`, the variant
`Variants/P521/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P521.PPC64LE.EcP521

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  Spec.EcKey.P521.publicKeyApi.artifact PPC64LE.target {
    notes := ["The function is `vg_ecdsa_p521_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it \
      saves `r14`, `r31` and `lr` in `scratch` (in `r3` during the function), and keeps `out` in \
      `r14`; field elements are nine 64-bit words in Montgomery form, multiplied by \
      word-by-word Montgomery multiplication (CIOS, in calls of `vg_p521_mul_mod_p` and the other \
      functions of `p521_mont`) with a final conditional subtraction; `[d]G` is a call of `vg_p521_mul`, a double-and-add \
      ladder over all 528 bits of the 66-byte encoding of `d`, with the complete addition formulas of Renes, Costello and \
      Batina for every addition and doubling (inlined, as calls of the field functions: the \
      points do not fit the point functions' slots) and a masked selection for each bit; and \
      `Z⁻¹` is Fermat's, by square-and-always-multiply over the bits of `p - 2`. The result (or zeros) is selected \
      by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."]
    code := Impl.EcKey.PPC64LE.publicKeyP521
    verified := Proof.EcKey.PPC64LE.P521.pk_verified h.law }]

end VG.Generic.P521.PPC64LE.EcP521
