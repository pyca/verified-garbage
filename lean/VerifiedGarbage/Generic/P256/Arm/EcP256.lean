module

public import VerifiedGarbage.Proof.EcKey.Arm.P256.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# P-256 public keys (FIPS 186-5 §A.2) on 32-bit ARM

A generic file (see `TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P256.Arm.EcP256

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.EcKey.P256.publicKeyApi.artifact Arm.target {
    notes := ["The function is `vg_ecdsa_p256_sign`'s code up to the inversion of `Z`, with \
      `d` as both the key and the secret number. `[d]G` uses the shared signed 7-bit comb: 37 \
      complete Renes–Costello–Batina additions and a 151552-byte Montgomery table. Each digit \
      scans all 64 entries in its public row and selects coordinates by masks. Field \
      arithmetic uses sixteen 16-bit Montgomery digits. `Z⁻¹` is Fermat's. The result (or \
      zeros) is selected by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on \
      the pointers."]
    consts := Impl.Weierstrass.Arm.p256CombConsts
    code := Impl.Ecdsa.Arm.publicKeyP256Comb
    verified := Proof.EcKey.Arm.P256.combPk_verified h.law }]

end VG.Generic.P256.Arm.EcP256
