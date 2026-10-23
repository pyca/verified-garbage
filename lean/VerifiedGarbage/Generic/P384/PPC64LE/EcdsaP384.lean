module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P384.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.Impl.Ecdsa.Verify.P384.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P384.Verified
public import VerifiedGarbage.Spec.Ecdsa.Verify.P384
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P384.Lit

/-!
# ECDSA signatures over P-384 (FIPS 186-5 §6.4.1) on PPC64LE

A generic file (see `TCB/Emit.lean`) over P-384's group law `h`, the variant
`Variants/P384/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P384.PPC64LE.EcdsaP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.Ecdsa.P384.signApi.artifact PPC64LE.target {
    notes := ["The function saves `r14`, `r31` and `lr` in \
      `scratch` (in `r3` during the function), and keeps `out` in `r14`. Field elements and \
      scalars are six 64-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication (CIOS, in calls of `vg_p384_mul_mod_p` and the other functions of \
      `p384_mont`) with a final conditional subtraction. `[k]G` is a double-and-add ladder over \
      all 384 bits of `k`, with the complete addition formulas of Renes, Costello and Batina for \
      every addition and doubling (calls of `vg_p384_point_double` and `vg_p384_point_add`) and a \
      masked selection for each bit; the inversions modulo `p` and `n` are Fermat's, by \
      square-and-always-multiply over the bits of `p - 2` and `n - 2`. The signature (or zeros) is \
      selected by a mask, so the time depends only on the pointers."]
    code := Impl.Ecdsa.PPC64LE.signP384
    verified := Proof.Ecdsa.PPC64LE.P384.sign_verified h.law },
  Spec.Ecdsa.P384.verifyApi.artifact PPC64LE.target {
    notes := ["The function is `vg_ecdsa_p384_sign`'s setup, \
      field arithmetic, ladder and inversions, with `vg_ecdh_p384`'s checks of the public key: it \
      saves `r14`, `r31` and `lr` in `scratch` (in `r3` during the function); field elements and \
      scalars are six 64-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication (CIOS, in calls of `vg_p384_mul_mod_p` and the other functions of \
      `p384_mont`) with a final conditional subtraction. The key is checked without branches (its \
      first byte, both coordinates below `p`, and the curve's equation), and the second ladder \
      multiplies the key's point if it is valid, else `G`, so it always runs on a point of the \
      curve. `s⁻¹` modulo `n` and `Z⁻¹` are Fermat's, by square-and-always-multiply; `[u]G` and \
      `[v]Q` are double-and-add ladders over all 384 bits of `u` and `v`, with the complete \
      addition formulas of Renes, Costello and Batina (calls of `vg_p384_point_double` and \
      `vg_p384_point_add` in the ladders), which also add the two. The result is the conjunction \
      of the checks (the key, `r` and `s` in `[1, n-1]`, the sum not the point at infinity, and \
      `x ≡ r` modulo `n`) as a mask, so the time depends only on the pointers, although the \
      contract would let every input affect it."]
    code := Impl.Ecdsa.Verify.PPC64LE.verifyP384
    verified := Proof.Ecdsa.Verify.PPC64LE.P384.verify_verified h.law }]

end VG.Generic.P384.PPC64LE.EcdsaP384
