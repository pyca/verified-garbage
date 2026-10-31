module

public import VerifiedGarbage.Proof.EcKey.Arm.P384.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# P-384 public keys (FIPS 186-5 §A.2) on 32-bit ARM

A generic file (see `TCB/Emit.lean`) over P-384's group law `h`, the variant
`Variants/P384/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P384.Arm.EcP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.EcKey.P384.publicKeyApi.artifact Arm.target {
    notes := ["The function is `vg_ecdsa_p384_sign`'s code up to the inversion of `Z`, with \
      `d` as both the key and the secret number. `[d]G` uses the shared signed 7-bit comb: 55 \
      complete Renes–Costello–Batina additions and a 337920-byte Montgomery table. Each digit \
      scans all 64 entries in its public row and selects coordinates by masks. Field \
      elements are twelve packed 32-bit words in Montgomery form. `Z⁻¹` is Fermat's. The result (or \
      zeros) is selected by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on \
      the pointers."]
    consts := Impl.Weierstrass.Arm.p384CombConsts
    code := Impl.Ecdsa.Arm.publicKeyP384Comb
    verified := Proof.EcKey.Arm.P384.combPk_verified h.law },
  Spec.EcKey.P384.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    notes := ["`vg_ec_p384_public_key`'s code, but for its calls of `vg_p384_point_add_umaal` in \
      the comb. Field multiplications are calls of `vg_p384_mul_mod_p_umaal` (and `vg_p384_mul_mod_n_umaal`), which multiply the numbers' 32-bit words with one `umaal` per word of each Montgomery row (`hi:lo = n m + hi + lo`)."]
    consts := Impl.Weierstrass.Arm.p384CombConsts
    code := Impl.Ecdsa.Arm.publicKeyP384CombU
    verified := Proof.EcKey.Arm.P384.combPkU_verified h.law
    features := ["umaal"] }]

end VG.Generic.P384.Arm.EcP384
