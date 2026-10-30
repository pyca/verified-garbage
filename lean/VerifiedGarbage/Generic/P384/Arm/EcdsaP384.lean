module

public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P384.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.P384
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# ECDSA over P-384 (FIPS 186-5) on 32-bit ARM

A generic file (see `TCB/Emit.lean`) over P-384's group law `h`, the variant
`Variants/P384/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P384.Arm.EcdsaP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.Ecdsa.P384.signApi.artifact Arm.target {
    notes := ["The function saves the callee-saved registers `r4`–`r11` and `lr` in `scratch`, \
      and keeps `out` in `lr` (in `r10` during the calls). `[k]G` uses the shared signed 7-bit \
      comb: 55 complete Renes–Costello–Batina additions and a 337920-byte Montgomery table. \
      Each digit scans all 64 entries in its public row and selects coordinates by masks. \
      Field elements and scalars are \
      twelve packed 32-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication (CIOS, with four half-word `mul` products per word product, in calls of \
      `vg_p384_mul_mod_p` and the other functions of `p384_mont`). Inversions modulo p and n use Fermat's theorem. The \
      signature (or zeros) is selected by a mask, so the time depends only on the pointers."]
    consts := Impl.Weierstrass.Arm.p384CombConsts
    code := Impl.Ecdsa.Arm.signP384Comb
    verified := Proof.Ecdsa.Arm.P384.combSign_verified h.law },
  Spec.Ecdsa.P384.verifyApi.artifact Arm.target {
    notes := ["The generator term [u]G uses the same signed 7-bit comb as signing (after \
      expanding `u` into the table of its bits), scanning each complete 64-entry table row. \
      The term [v]Q is a call of `vg_p384_mul`, a double-and-add ladder over all 384 bits of \
      `v`. Both use complete Renes–Costello–Batina addition formulas, which also add the two. \
      The key is checked without branches (its first byte, both coordinates below `p`, and \
      the curve's equation), and the ladder multiplies the key's point if it is valid, else \
      `G`. `s⁻¹` modulo `n` and `Z⁻¹` are Fermat's. The result is the conjunction of the \
      checks as a mask, so the time depends only on the pointers, although the contract would \
      let every input affect it."]
    consts := Impl.Weierstrass.Arm.p384CombConsts
    code := Impl.Ecdsa.Arm.verifyP384Comb
    verified := Proof.Ecdsa.Verify.Arm.P384.combVerify_verified h.law }]

end VG.Generic.P384.Arm.EcdsaP384
