import VerifiedGarbage.Proof.Framework.PowLit
import Mathlib.Data.Int.ModEq
import Mathlib.Data.BitVec
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Signed 32-bit words, shifts, and matrix combinations -/
namespace VG.Proof.Divstep.W32

/-- `W ≡ x (mod 2H)`, `W ∈ [0, 2H)`, `x ∈ [-H, H)`: `W` is `x`, or `x + 2H` if negative. -/
theorem tc_eq {H x W : Int} (hH : 0 < H) (hx1 : -H ≤ x) (hx2 : x < H) (hW0 : 0 ≤ W) (hW1 : W < 2 * H)
    (hc : W % (2 * H) = x % (2 * H)) : W = x + if x < 0 then 2 * H else 0 := by
  have hc'' : W ≡ x [ZMOD 2 * H] := hc
  obtain ⟨c, hc'⟩ := hc''.dvd
  have c1 : c ≤ 0 := by
    by_contra h; push Not at h
    have : 2 * H * 1 ≤ 2 * H * c := mul_le_mul_of_nonneg_left (by omega) (by omega)
    linarith
  have c2 : -1 ≤ c := by
    by_contra h; push Not at h
    have : 2 * H * c ≤ 2 * H * (-2) := mul_le_mul_of_nonneg_left (by omega) (by omega)
    linarith
  split
  · have : c = -1 := by
      by_contra h
      have : c = 0 := by omega
      subst this; linarith
    subst this; linarith
  · have : c = 0 := by
      by_contra h
      have : c = -1 := by omega
      subst this; linarith
    subst this; linarith

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
    split <;> ring
  rw [hD, e, Int.mul_ediv_cancel_left _ (by norm_num), Int.emod_emod_of_dvd _ (dvd_refl _)]
  split
  · rw [show z + 2 * H * 2 ^ 2 = z + 2 * H * 2 ^ 2 from rfl, Int.add_mul_emod_self_left]
  · rw [Int.add_zero]

/-- The masked linear combination: unsigned products less `2^32` times the
other factor where a word is negative is the signed combination, modulo `M`,
given `2^32 X' ≡ 2^32 X` (the factor's words but the top). -/
theorem lin_words {M V X X' Y Y' W W' : Int} {c c' : Prop} [Decidable c] [Decidable c']
    (hX : (2 ^ 32 * X') % M = (2 ^ 32 * X) % M) (hY : (2 ^ 32 * Y') % M = (2 ^ 32 * Y) % M)
    (h : (V + 2 ^ 32 * ((if c then X' else 0) + (if c' then Y' else 0))) % M = (W * X + W' * Y) % M) :
    V % M = ((W - if c then 2 ^ 32 else 0) * X + (W' - if c' then 2 ^ 32 else 0) * Y) % M := by
  have h1 : V ≡ W * X + W' * Y - 2 ^ 32 * ((if c then X' else 0) + (if c' then Y' else 0)) [ZMOD M] := by
    have := Int.ModEq.sub_right (2 ^ 32 * ((if c then X' else 0) + (if c' then Y' else 0))) h
    simpa using this
  have h2 : 2 ^ 32 * ((if c then X' else 0) + (if c' then Y' else 0)) ≡
      2 ^ 32 * ((if c then X else 0) + (if c' then Y else 0)) [ZMOD M] := by
    have hX' : 2 ^ 32 * X' ≡ 2 ^ 32 * X [ZMOD M] := hX
    have hY' : 2 ^ 32 * Y' ≡ 2 ^ 32 * Y [ZMOD M] := hY
    split_ifs <;> simp only [mul_add, mul_zero, add_zero, zero_add]
    · exact hX'.add hY'
    · exact hX'
    · exact hY'
    · rfl
  have h3 := h1.trans (Int.ModEq.sub_left _ h2)
  rw [h3]
  congr 1
  split_ifs <;> ring

/-- A word as a signed number. -/
theorem toInt_sgn (w : BitVec 32) : (w.toNat : Int) - (if 2 ^ 31 ≤ w.toNat then 2 ^ 32 else 0) = w.toInt := by
  rw [BitVec.toInt_eq_toNat_cond]
  have := w.isLt
  split_ifs <;> push_cast <;> omega

/-- `shr_words` on natural numbers, as words hold them (`c = 2^30`, `B = 2^32`). -/
theorem shr_nat {H V D c B : Nat} {y z : Int} (hc : 2 ^ 30 = c) (hB : 2 ^ 32 = B) (hH : 0 < H) (hV1 : V < 2 * H)
    (hVy : (V : Int) % ((2 * H : Nat) : Int) = y % ((2 * H : Nat) : Int)) (hy1 : -(H : Int) ≤ y) (hy2 : y < H)
    (hz : y = 2 ^ 30 * z) (hD : D = (V + 2 * H * (if H ≤ V then B - 1 else 0)) / c % (2 * H)) :
    (D : Int) % ((2 * H : Nat) : Int) = z % ((2 * H : Nat) : Int) := by
  have hB1 : 1 ≤ B := by rw [← hB]; exact Nat.one_le_two_pow
  have hc' : (c : Int) = 2 ^ 30 := by rw [← hc]; norm_num
  have hB' : (B : Int) = 2 ^ 32 := by rw [← hB]; norm_num
  have hz' : y = (c : Int) * z := by rw [hc']; exact hz
  have hD' := congrArg (Nat.cast : Nat → Int) hD
  push_cast [Nat.cast_sub hB1] at hD' hVy ⊢
  rw [← ite_natCast_le] at hD'
  exact shr_words hc' hB' (by exact_mod_cast hH) (by omega) (by exact_mod_cast hV1) hVy hy1 hy2 hz' hD'

/-- A small integer's word, as a signed number. -/
theorem toInt_small {u : Int} (h : |u| ≤ 2 ^ 30) : (BitVec.ofInt 32 u).toInt = u := by
  rw [abs_le] at h
  exact BitVec.toInt_ofInt_eq_self (by decide) (by norm_num; omega) (by norm_num; omega)

/-- The combination of congruent numbers. -/
theorem cong_comb {Q u v X Y f g : Int} (hX : X % Q = f % Q) (hY : Y % Q = g % Q) :
    (u * X + v * Y) % Q = (u * f + v * g) % Q :=
  Int.ModEq.add (Int.ModEq.mul_left u hX) (Int.ModEq.mul_left v hY)

/-- A batch's combination of numbers at most `p`. -/
theorem comb_le {u v f g p : Int} (huv : |u| + |v| ≤ 2 ^ 30) (hf : |f| ≤ p) (hg : |g| ≤ p) :
    |u * f + v * g| ≤ 2 ^ 30 * p := by
  have hp : 0 ≤ p := le_trans (abs_nonneg _) hf
  calc |u * f + v * g| ≤ |u| * |f| + |v| * |g| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |u| * p + |v| * p := add_le_add (mul_le_mul_of_nonneg_left hf (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hg (abs_nonneg _))
    _ = (|u| + |v|) * p := by ring
    _ ≤ 2 ^ 30 * p := mul_le_mul_of_nonneg_right huv hp

/-- Within the half range of `L` words, for `p < 2^(32 (L - 1))`. -/
theorem comb_range {u v f g : Int} {p A : Nat} (huv : |u| + |v| ≤ 2 ^ 30) (hf : |f| ≤ p) (hg : |g| ≤ p)
    (hpA : p < A) : -((A * 2 ^ 31 : Nat) : Int) ≤ u * f + v * g ∧ u * f + v * g < ((A * 2 ^ 31 : Nat) : Int) := by
  have h := comb_le huv hf hg
  rw [abs_le] at h
  have hpA' : (p : Int) < A := by exact_mod_cast hpA
  have hp0 : (0 : Int) ≤ p := Int.natCast_nonneg _
  push_cast
  constructor <;> nlinarith

/-! ## Bounds over a run -/

end VG.Proof.Divstep.W32
