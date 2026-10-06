import VerifiedGarbage.Proof.Gcm.Poly
import VerifiedGarbage.Spec.Gcm.Precomputed

/-!
# GCM: the powers of the hash subkey, in the field

`Spec.Gcm.hpow h k` is `hᵏ` in `Q` (`φ_hpow`): `Spec.Gcm.one` stands for 1.
-/

namespace VG.Proof.Gcm.Poly

open Polynomial

theorem gp_one : gp Spec.Gcm.one = 1 := by
  rw [show Spec.Gcm.one = (1#1 ++ 0#127 : BitVec 128) by decide, gp_append, gp_zero', mul_zero, add_zero]
  ext k
  rw [coeff_gp, coeff_one]
  rcases k with _ | k
  · rfl
  · simp only [BitVec.getMsbD, show ¬ (k + 1 < 1) by omega, decide_false, Bool.false_and]; rfl

theorem φ_one : φ Spec.Gcm.one = 1 := by
  rw [φ, gp_one, map_one]

theorem φ_hpow (h : Spec.Gcm.Block) (k : Nat) : φ (Spec.Gcm.hpow h k) = φ h ^ k := by
  induction k with
  | zero => exact φ_one
  | succ k ih =>
    show φ (Spec.Gcm.mul (Spec.Gcm.hpow h k) h) = _
    rw [φ_mul, ih, pow_succ]

end VG.Proof.Gcm.Poly
