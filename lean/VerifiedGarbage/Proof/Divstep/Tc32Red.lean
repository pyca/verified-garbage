module
public import VerifiedGarbage.Proof.Divstep.Alg32Def

import VerifiedGarbage.Proof.Divstep.Mred32
import VerifiedGarbage.Proof.Divstep.Tc32Words
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Positivity.Core
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.BitVec
import Mathlib.Tactic.Linarith

/-! # Signed Montgomery reduction on multiword values -/

@[expose] public section

namespace VG.Proof.Divstep.W32

/-- `-p < mredRaw t < 2p` for `|t| ≤ 2^31 p`. -/
theorem mredRaw_range {p m t : Int} (hp : 0 < p) (hm : (p * m + 1) % 2 ^ 32 = 0) (ht : |t| ≤ 2 ^ 31 * p) :
    -p < mredRaw p m t ∧ mredRaw p m t < 2 * p := by
  have hraw := mredRaw_spec (t := t) hm
  have hk0 : 0 ≤ (t * m) % 2 ^ 32 := Int.emod_nonneg _ (by norm_num)
  have hk1 : (t * m) % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by norm_num)
  rw [abs_le] at ht
  constructor
  · by_contra h; push Not at h
    have : 2 ^ 32 * mredRaw p m t ≤ 2 ^ 32 * (-p) := by nlinarith
    nlinarith
  · by_contra h; push Not at h
    have : 2 ^ 32 * (2 * p) ≤ 2 ^ 32 * mredRaw p m t := by nlinarith
    nlinarith

/-- `mred` as the code computes it, on words of `n + 1` (`A = 2^(32 n)`, `p < A`):
`W` holds `t`; `E` the sum `W + A 2^32 S + k p` modulo `A 2^64`, for `W`'s sign
word `S` and `k ≡ W m`; `R` its words above the lowest; `R₁ = R + p` if
negative; `R₂ = R₁ - p`; `R₃ = R₂ + p` if negative. -/
theorem mred_first_words {A B H p m t W k E R R₁ : Int} (hB : B = 2 ^ 32) (hH : H = 2 ^ 31) (hA : 0 < A)
    (hp : 0 < p) (hpA : p < A) (hm : (p * m + 1) % B = 0) (ht : |t| ≤ 2 ^ 31 * p)
    (hW0 : 0 ≤ W) (hW1 : W < A * B) (hWt : W % (A * B) = t % (A * B))
    (hk0 : 0 ≤ k) (hk1 : k < B) (hk : k % B = (W * m) % B)
    (hE : E = (W + A * B * (if A * H ≤ W then B - 1 else 0) + k * p) % (A * B * B))
    (hR : R = E / B)
    (hR₁ : R₁ = (R + if A * H ≤ R then p else 0) % (A * B))
    : R₁ = mredRaw p m t + if mredRaw p m t < 0 then p else 0 := by
  subst hB hH
  have hH : 0 < A * 2 ^ 31 := by positivity
  have hQ : A * 2 ^ 32 = 2 * (A * 2 ^ 31) := by ring
  have hpH : 2 * p < A * 2 ^ 31 := by omega_arith
  rw [abs_le] at ht
  have htH : -(A * 2 ^ 31) ≤ t ∧ t < A * 2 ^ 31 := by
    constructor <;> omega_arith
  -- `W` holds `t`.
  have eW := tc_eq hH htH.1 htH.2 hW0 (by rw [← hQ]; exact hW1) (by rw [← hQ]; exact hWt)
  have sW := tc_neg htH.1 htH.2 eW
  -- `k = t m mod 2^32`.
  have hk' : k = (t * m) % 2 ^ 32 := by
    have h32 : (2 : Int) ^ 32 ∣ A * 2 ^ 32 := dvd_mul_left _ _
    have hWt' : W % 2 ^ 32 = t % 2 ^ 32 := by
      rw [← Int.emod_emod_of_dvd W h32, ← Int.emod_emod_of_dvd t h32, hWt]
    rw [← Int.emod_eq_of_lt hk0 hk1, hk, Int.mul_emod, hWt', ← Int.mul_emod]
  -- The sum is `t + k p = 2^32 r`, in two's complement.
  set r := mredRaw p m t with hr
  have hraw : 2 ^ 32 * r = t + (t * m) % 2 ^ 32 * p := mredRaw_spec hm
  rw [← hk'] at hraw
  obtain ⟨rlo, rhi⟩ := mredRaw_range hp hm (abs_le.mpr ⟨by omega_arith, ht.2⟩)
  rw [← hr] at rlo rhi
  have hE' : E = 2 ^ 32 * (r + if r < 0 then A * 2 ^ 32 else 0) := by
    have hX : W + A * 2 ^ 32 * (if A * 2 ^ 31 ≤ W then 2 ^ 32 - 1 else 0) + k * p =
        2 ^ 32 * r + (if r < 0 then A * 2 ^ 32 * 2 ^ 32 else 0) + A * 2 ^ 32 * 2 ^ 32 *
          ((if t < 0 then 1 else 0) - (if r < 0 then 1 else 0)) := by
      have hS : (if A * 2 ^ 31 ≤ W then (2 : Int) ^ 32 - 1 else 0) = if t < 0 then 2 ^ 32 - 1 else 0 := by
        simp only [sW]
      have hkp : k * p = 2 ^ 32 * r - t := by omega_arith
      rw [hS, eW, hkp]
      by_cases h1 : t < 0 <;> by_cases h2 : r < 0 <;> simp only [h1, h2, ↓reduceIte] <;> ring
    rw [hE, hX, Int.add_mul_emod_self_left]
    have h0 : 0 ≤ 2 ^ 32 * r + (if r < 0 then A * 2 ^ 32 * 2 ^ 32 else 0) := by
      split <;> omega_arith
    have h1 : 2 ^ 32 * r + (if r < 0 then A * 2 ^ 32 * 2 ^ 32 else 0) < A * 2 ^ 32 * 2 ^ 32 := by
      split <;> omega_arith
    rw [Int.emod_eq_of_lt h0 h1]
    split <;> ring
  have eR : R = r + if r < 0 then 2 * (A * 2 ^ 31) else 0 := by
    rw [hR, hE', Int.mul_ediv_cancel_left _ (by norm_num), hQ]
  have rH : -(A * 2 ^ 31) ≤ r ∧ r < A * 2 ^ 31 := ⟨by omega_arith, by omega_arith⟩
  have sR := tc_neg rH.1 rH.2 eR
  -- `R₁ = r + p` if negative, else `r`.
  have eR₁ : R₁ = r + if r < 0 then p else 0 := by
    have hc : (if A * 2 ^ 31 ≤ R then p else 0) = if r < 0 then p else 0 := by simp only [sR]
    rw [hR₁, hc, eR, hQ]
    by_cases h : r < 0
    · simp only [h, ↓reduceIte]
      rw [show r + 2 * (A * 2 ^ 31) + p = r + p + 2 * (A * 2 ^ 31) * 1 by ring, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt (by omega_arith) (by omega_arith)]
    · simp only [h, ↓reduceIte, Int.add_zero]
      rw [Int.emod_eq_of_lt (by omega_arith) (by omega_arith)]
  exact eR₁

end VG.Proof.Divstep.W32
