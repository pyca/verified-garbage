module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.BrainpoolP512r1.PPC64LE
public import VerifiedGarbage.Proof.EcKey.PPC64LE.BrainpoolP512r1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
import VerifiedGarbage.Proof.EcKey.PPC64LE.BrainpoolP512r1.Lit

/-!
# brainpoolP512r1 public keys (FIPS 186-5 §A.2) on PPC64LE

A generic file (see `TCB/Emit.lean`) over brainpoolP512r1's group law `h`, the variant
`Variants/BrainpoolP512r1/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.PPC64LE.EcBrainpoolP512r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP512r1.curve) : List Artifact := [
  Spec.EcKey.BrainpoolP512r1.publicKeyApi.artifact PPC64LE.target {
    notes := ["The function is `vg_ecdsa_brainpoolp512r1_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it \
      saves `r14`, `r31` and `lr` in `scratch` (in `r3` during the function), and keeps `out` in \
      `r14`; field elements are eight 64-bit words in Montgomery form, multiplied by \
      word-by-word Montgomery multiplication (CIOS, in calls of `vg_brainpoolp512r1_mul_mod_p` and the other \
      functions of `brainpoolp512r1_mont`) with a final conditional subtraction; `[d]G` is a double-and-add \
      ladder over all 512 bits of `d`, with the complete addition formulas of Renes, Costello and \
      Batina for every addition and doubling (inlined, as calls of the field functions: the \
      points do not fit the point functions' slots) and a masked selection for each bit; and \
      `Z⁻¹` is Fermat's, by square-and-always-multiply over the bits of `p - 2`. The result (or zeros) is selected \
      by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."]
    code := Impl.EcKey.PPC64LE.publicKeyBrainpoolP512r1
    verified := Proof.EcKey.PPC64LE.BrainpoolP512r1.pk_verified h.law }]

end VG.Generic.BrainpoolP512r1.PPC64LE.EcBrainpoolP512r1
