module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Secp256k1.PPC64LE
public import VerifiedGarbage.Proof.EcKey.PPC64LE.Secp256k1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.Secp256k1
import VerifiedGarbage.Proof.EcKey.PPC64LE.Secp256k1.Lit

/-!
# secp256k1 public keys (FIPS 186-5 §A.2) on PPC64LE

A generic file (see `TCB/Emit.lean`) over secp256k1's group law `h`, the variant
`Variants/Secp256k1/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.Secp256k1.PPC64LE.EcSecp256k1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact := [
  Spec.EcKey.Secp256k1.publicKeyApi.artifact PPC64LE.target {
    notes := ["The function is `vg_ecdsa_secp256k1_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it \
      saves `r14`, `r31` and `lr` in `scratch` (in `r3` during the function), and keeps `out` in \
      `r14`; field elements are four 64-bit words in Montgomery form, multiplied by \
      word-by-word Montgomery multiplication (CIOS, in calls of `vg_secp256k1_mul_mod_p` and the other \
      functions of `secp256k1_mont`) with a final conditional subtraction; `[d]G` is a double-and-add \
      ladder over all 256 bits of `d`, with the complete addition formulas of Renes, Costello and \
      Batina for every addition and doubling (calls of `vg_secp256k1_point_double_a0` and \
      `vg_secp256k1_point_add_affine_a0`, Algorithms 9 and 8 for `a = 0`) and a masked selection for each bit; and `Z⁻¹` is Fermat's, \
      by square-and-always-multiply over the bits of `p - 2`. The result (or zeros) is selected \
      by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."]
    code := Impl.EcKey.PPC64LE.publicKeySecp256k1
    verified := Proof.EcKey.PPC64LE.Secp256k1.pk_verified h.law }]

end VG.Generic.Secp256k1.PPC64LE.EcSecp256k1
