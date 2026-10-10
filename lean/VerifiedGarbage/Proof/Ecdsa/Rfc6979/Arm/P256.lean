import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
import VerifiedGarbage.Proof.Ecdsa.Arm.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# Deterministic ECDSA on 32-bit ARM: P-256

P-256 as the proof's curve (`p256`): scalars of 4 64-bit words, the order
`n` of exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_p256_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at P-256's sizes, which is `Proof.Ecdsa.Arm.signArm`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm

theorem p256_nBits : Spec.Ecdsa.nBits Spec.P256.curve = 256 := by
  show Spec.P256.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.P256.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P256.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- P-256, with the group law `hL`. -/
def p256 (hL : Weierstrass.Law Spec.P256.curve) : RfcCurve where
  E := Impl.Ecdsa.Arm.p256
  inst := Spec.Ecdsa.P256.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr (.inl rfl), rfl, p256_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 32 - Spec.Ecdsa.nBits Spec.P256.curve = 0; rw [p256_nBits]
  coreN := Spec.Ecdsa.P256.signApi.name
  coreC := Impl.Ecdsa.Arm.signP256
  coreX := Proof.Ecdsa.Arm.sign_arm hL
  coreCT := Proof.Ecdsa.Arm.sign_ct
  coreStack := by lit_decide
  reduceT := Function.const _ ⟨_, by taint_decide⟩

end VG.Proof.Ecdsa.Rfc6979.Arm
