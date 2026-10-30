module

public import VerifiedGarbage.Proof.Ecdsa.Arm.P256.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P256.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.P256
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# ECDSA over P-256 (FIPS 186-5) on 32-bit ARM

A generic file (see `TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P256.Arm.EcdsaP256

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.Ecdsa.P256.signApi.artifact Arm.target {
    notes := ["The function saves the callee-saved registers `r4`–`r11` and `lr` in `scratch`, \
      and keeps `out` in `lr` (in `r10` during the calls). `[k]G` uses the shared signed 7-bit \
      comb: 37 complete Renes–Costello–Batina additions and a 151552-byte Montgomery table. \
      Each digit scans all 64 entries in its public row and selects coordinates by masks. \
      Field elements and scalars are sixteen 16-bit digits in Montgomery form, multiplied by \
      digit-by-digit Montgomery multiplication (CIOS, in calls of `vg_p256_mul_mod_p` and the \
      other functions of `p256_mont`). Inversions modulo p and n use Fermat's theorem. The \
      signature (or zeros) is selected by a mask, so the time depends only on the pointers."]
    consts := Impl.Weierstrass.Arm.p256CombConsts
    code := Impl.Ecdsa.Arm.signP256Comb
    verified := Proof.Ecdsa.Arm.P256.combSign_verified h.law },
  Spec.Ecdsa.P256.verifyApi.artifact Arm.target {
    notes := ["The generator term [u]G uses the same signed 7-bit comb as signing (after \
      expanding `u` into the table of its bits), scanning each complete 64-entry table row. \
      The term [v]Q is a call of `vg_p256_mul`, a double-and-add ladder over all 256 bits of \
      `v`. Both use complete Renes–Costello–Batina addition formulas, which also add the two. \
      The key is checked without branches (its first byte, both coordinates below `p`, and \
      the curve's equation), and the ladder multiplies the key's point if it is valid, else \
      `G`. `s⁻¹` modulo `n` and `Z⁻¹` are Fermat's. The result is the conjunction of the \
      checks as a mask, so the time depends only on the pointers, although the contract would \
      let every input affect it."]
    consts := Impl.Weierstrass.Arm.p256CombConsts
    code := Impl.Ecdsa.Arm.verifyP256Comb
    verified := Proof.Ecdsa.Verify.Arm.P256.combVerify_verified h.law }]

end VG.Generic.P256.Arm.EcdsaP256
