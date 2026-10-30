module

public import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP256r1.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# brainpoolP256r1 public keys (FIPS 186-5 §A.2) on 32-bit ARM

A generic file (see `TCB/Emit.lean`) over brainpoolP256r1's group law `h`, the variant
`Variants/BrainpoolP256r1/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.Arm.EcBrainpoolP256r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve) : List Artifact := [
  Spec.EcKey.BrainpoolP256r1.publicKeyApi.artifact Arm.target {
    notes := ["The function is `vg_ecdsa_brainpoolp256r1_sign`'s code up to the inversion of `Z`, with \
      `d` as both the key and the secret number. `[d]G` uses the shared signed 7-bit comb: 37 \
      complete Renes–Costello–Batina additions and a 151552-byte Montgomery table. Each digit \
      scans all 64 entries in its public row and selects coordinates by masks. Field \
      arithmetic uses sixteen 16-bit Montgomery digits. `Z⁻¹` is Fermat's. The result (or \
      zeros) is selected by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on \
      the pointers."]
    consts := Impl.Weierstrass.Arm.brainpoolp256r1CombConsts
    code := Impl.Ecdsa.Arm.publicKeyBrainpoolP256r1Comb
    verified := Proof.EcKey.Arm.BrainpoolP256r1.combPk_verified h.law }]

end VG.Generic.BrainpoolP256r1.Arm.EcBrainpoolP256r1
