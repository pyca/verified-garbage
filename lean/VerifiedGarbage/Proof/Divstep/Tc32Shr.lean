module

public import VerifiedGarbage.Proof.Framework.PowLit
public import Mathlib.Data.Int.ModEq

/-! # Signed 32-bit words: the arithmetic shift by 30

The facts of `Tc32Words.lean` that need no algebra, so that modules many
others import (a batched inverse's coefficients, `Red30.lean`) can use them:
a word in `[0, 2H)` congruent to `x ∈ [-H, H)` is `x`, or `x + 2H` if
negative (`tc_eq`), its sign is its top half (`tc_neg`), and the shift by 30
with the sign word appended divides by `2^30` modulo `2H` (`shr_words`,
`shr_nat`).
-/

@[expose] public section

namespace VG.Proof.Divstep.W32

/-- `W ≡ x (mod 2H)`, `W ∈ [0, 2H)`, `x ∈ [-H, H)`: `W` is `x`, or `x + 2H` if negative. -/
theorem tc_eq {H x W : Int} (_hH : 0 < H) (hx1 : -H ≤ x) (hx2 : x < H) (hW0 : 0 ≤ W) (hW1 : W < 2 * H)
    (hc : W % (2 * H) = x % (2 * H)) : W = x + if x < 0 then 2 * H else 0 := by
  rw [Int.emod_eq_of_lt hW0 hW1] at hc
  split
  · rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)] at hc
    exact hc
  · rw [Int.emod_eq_of_lt (by omega) (by omega)] at hc
    omega

/-- The sign of such a word: its top half. -/
theorem tc_neg {H x W : Int} (hx1 : -H ≤ x) (hx2 : x < H)
    (h : W = x + if x < 0 then 2 * H else 0) : (H ≤ W ↔ x < 0) := by
  split at h <;> constructor <;> intro <;> omega

/-- `mred_words` on natural numbers, as words hold them. -/
theorem ite_natCast_le {a b : Nat} {x y : Int} : (if (a : Int) ≤ b then x else y) = if a ≤ b then x else y := by
  by_cases h : a ≤ b
  · simp only [h, Int.ofNat_le.mpr h, ↓reduceIte]
  · have h' : ¬ (a : Int) ≤ b := fun h' => h (Int.ofNat_le.mp h')
    simp only [h, h', ↓reduceIte]

/-- The arithmetic shift by 30 of `y = 2^30 z` held in `[0, 2H)` (two's complement), its
sign word appended: `z`, modulo `2H`. -/
theorem shr_words {H V y z D c B : Int} (hc : c = 2 ^ 30) (hB : B = 2 ^ 32) (hH : 0 < H) (hV0 : 0 ≤ V)
    (hV1 : V < 2 * H) (hVy : V % (2 * H) = y % (2 * H)) (hy1 : -H ≤ y) (hy2 : y < H) (hz : y = c * z)
    (hD : D = ((V + 2 * H * (if H ≤ V then B - 1 else 0)) / c) % (2 * H)) :
    D % (2 * H) = z % (2 * H) := by
  subst hc hB
  have eV := tc_eq hH hy1 hy2 hV0 hV1 hVy
  have sV := tc_neg hy1 hy2 eV
  have e : V + 2 * H * (if H ≤ V then 2 ^ 32 - 1 else 0) = 2 ^ 30 * (z + (if y < 0 then 2 * H * 2 ^ 2 else 0)) := by
    have hc : (if H ≤ V then (2 : Int) ^ 32 - 1 else 0) = if y < 0 then 2 ^ 32 - 1 else 0 := by simp only [sV]
    rw [hc, eV, hz]
    split <;> omega
  rw [hD, e, Int.mul_ediv_cancel_left _ (by decide), Int.emod_emod_of_dvd _ (dvd_refl _)]
  split
  · rw [Int.add_mul_emod_self_left]
  · rw [Int.add_zero]

/-- `shr_words` on natural numbers, as words hold them (`c = 2^30`, `B = 2^32`). -/
theorem shr_nat {H V D c B : Nat} {y z : Int} (hc : 2 ^ 30 = c) (hB : 2 ^ 32 = B) (hH : 0 < H) (hV1 : V < 2 * H)
    (hVy : (V : Int) % ((2 * H : Nat) : Int) = y % ((2 * H : Nat) : Int)) (hy1 : -(H : Int) ≤ y) (hy2 : y < H)
    (hz : y = 2 ^ 30 * z) (hD : D = (V + 2 * H * (if H ≤ V then B - 1 else 0)) / c % (2 * H)) :
    (D : Int) % ((2 * H : Nat) : Int) = z % ((2 * H : Nat) : Int) := by
  have hB1 : 1 ≤ B := by rw [← hB]; exact Nat.one_le_two_pow
  have hc' : (c : Int) = 2 ^ 30 := by rw [← hc]; push_cast
  have hB' : (B : Int) = 2 ^ 32 := by rw [← hB]; push_cast
  have hz' : y = (c : Int) * z := by rw [hc']; exact hz
  have hD' := congrArg (Nat.cast : Nat → Int) hD
  have e : ((if H ≤ V then B - 1 else 0 : Nat) : Int) = if (H : Int) ≤ V then (B : Int) - 1 else 0 := by
    by_cases h : H ≤ V
    · rw [ite_eq_left h, ite_eq_left (Int.ofNat_le.mpr h), Int.ofNat_sub hB1]; rfl
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (Int.ofNat_le.mp h'))]; rfl
  push_cast [e] at hD' hVy ⊢
  exact shr_words hc' hB' (by exact_mod_cast hH) (by omega) (by exact_mod_cast hV1) hVy hy1 hy2 hz' hD'

end VG.Proof.Divstep.W32
