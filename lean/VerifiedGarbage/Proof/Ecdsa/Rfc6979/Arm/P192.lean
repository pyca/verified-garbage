import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Lit
import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# Deterministic ECDSA on 32-bit ARM: P-192

P-192 as the proof's curve (`p192`): scalars of 3 64-bit words, the order
`n` of exactly 192 bits with `2^192 < 2 n`, and `vg_ecdsa_p192_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at P-192's sizes, which is `Proof.Ecdsa.Arm.P192.signArm`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm

theorem p192_nBits : Spec.Ecdsa.nBits Spec.P192.curve = 192 := by
  show Spec.P192.curve.n.log2 + 1 = 192
  have h₁ : 191 ≤ Spec.P192.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P192.curve.n.log2 < 192 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- P-192, with the group law `hL`. -/
def p192 (hL : Weierstrass.Law Spec.P192.curve) : RfcCurve where
  E := Impl.Ecdsa.Arm.p192
  inst := Spec.Ecdsa.P192.inst
  curve := rfl
  wide := false
  sizes := ⟨.inl rfl, rfl, p192_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 24 - Spec.Ecdsa.nBits Spec.P192.curve = 0; rw [p192_nBits]
  coreN := Spec.Ecdsa.P192.signApi.name
  coreC := Impl.Ecdsa.Arm.signP192
  coreX := Proof.Ecdsa.Arm.P192.sign_arm hL
  coreCT := Proof.Ecdsa.Arm.P192.sign_ct
  coreStack := by lit_decide
  reduceT := Function.const _ ⟨_, by taint_decide⟩

end VG.Proof.Ecdsa.Rfc6979.Arm
