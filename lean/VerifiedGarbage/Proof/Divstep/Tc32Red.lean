import VerifiedGarbage.Proof.Divstep.Mred32

/-! # Signed Montgomery reduction on multiword values -/
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
  have hpH : 2 * p < A * 2 ^ 31 := by omega
  rw [abs_le] at ht
  have htH : -(A * 2 ^ 31) ≤ t ∧ t < A * 2 ^ 31 := by
    constructor <;> omega
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
  obtain ⟨rlo, rhi⟩ := mredRaw_range hp hm (abs_le.mpr ⟨by omega, ht.2⟩)
  rw [← hr] at rlo rhi
  have hE' : E = 2 ^ 32 * (r + if r < 0 then A * 2 ^ 32 else 0) := by
    have hX : W + A * 2 ^ 32 * (if A * 2 ^ 31 ≤ W then 2 ^ 32 - 1 else 0) + k * p =
        2 ^ 32 * r + (if r < 0 then A * 2 ^ 32 * 2 ^ 32 else 0) + A * 2 ^ 32 * 2 ^ 32 *
          ((if t < 0 then 1 else 0) - (if r < 0 then 1 else 0)) := by
      have hS : (if A * 2 ^ 31 ≤ W then (2 : Int) ^ 32 - 1 else 0) = if t < 0 then 2 ^ 32 - 1 else 0 := by
        simp only [sW]
      have hkp : k * p = 2 ^ 32 * r - t := by omega
      rw [hS, eW, hkp]
      by_cases h1 : t < 0 <;> by_cases h2 : r < 0 <;> simp only [h1, h2, ↓reduceIte] <;> ring
    rw [hE, hX, Int.add_mul_emod_self_left]
    have h0 : 0 ≤ 2 ^ 32 * r + (if r < 0 then A * 2 ^ 32 * 2 ^ 32 else 0) := by
      split <;> omega
    have h1 : 2 ^ 32 * r + (if r < 0 then A * 2 ^ 32 * 2 ^ 32 else 0) < A * 2 ^ 32 * 2 ^ 32 := by
      split <;> omega
    rw [Int.emod_eq_of_lt h0 h1]
    split <;> ring
  have eR : R = r + if r < 0 then 2 * (A * 2 ^ 31) else 0 := by
    rw [hR, hE', Int.mul_ediv_cancel_left _ (by norm_num), hQ]
  have rH : -(A * 2 ^ 31) ≤ r ∧ r < A * 2 ^ 31 := ⟨by omega, by omega⟩
  have sR := tc_neg rH.1 rH.2 eR
  -- `R₁ = r + p` if negative, else `r`.
  have eR₁ : R₁ = r + if r < 0 then p else 0 := by
    have hc : (if A * 2 ^ 31 ≤ R then p else 0) = if r < 0 then p else 0 := by simp only [sR]
    rw [hR₁, hc, eR, hQ]
    by_cases h : r < 0
    · simp only [h, ↓reduceIte]
      rw [show r + 2 * (A * 2 ^ 31) + p = r + p + 2 * (A * 2 ^ 31) * 1 by ring, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt (by omega) (by omega)]
    · simp only [h, ↓reduceIte, Int.add_zero]
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
  exact eR₁

theorem mred_words {A B H p m t W k E R R₁ R₂ R₃ : Int} (hB : B = 2 ^ 32) (hH : H = 2 ^ 31) (hA : 0 < A)
    (hp : 0 < p) (hpA : p < A) (hm : (p * m + 1) % B = 0) (ht : |t| ≤ 2 ^ 31 * p)
    (hW0 : 0 ≤ W) (hW1 : W < A * B) (hWt : W % (A * B) = t % (A * B))
    (hk0 : 0 ≤ k) (hk1 : k < B) (hk : k % B = (W * m) % B)
    (hE : E = (W + A * B * (if A * H ≤ W then B - 1 else 0) + k * p) % (A * B * B))
    (hR : R = E / B)
    (hR₁ : R₁ = (R + if A * H ≤ R then p else 0) % (A * B))
    (hR₂0 : 0 ≤ R₂) (hR₂1 : R₂ < A * B) (hR₂ : (R₂ + p) % (A * B) = R₁)
    (hR₃ : R₃ = (R₂ + if A * H ≤ R₂ then p else 0) % (A * B)) :
    R₃ = mred p m t := by
  have eR₁ := mred_first_words hB hH hA hp hpA hm ht hW0 hW1 hWt hk0 hk1 hk hE hR hR₁
  subst hB hH
  have hH : 0 < A * 2 ^ 31 := by positivity
  have hQ : A * 2 ^ 32 = 2 * (A * 2 ^ 31) := by ring
  have hpH : 2 * p < A * 2 ^ 31 := by omega
  set r := mredRaw p m t with hr
  obtain ⟨rlo, rhi⟩ := mredRaw_range hp hm ht
  rw [← hr] at rlo rhi
  -- `R₂ = R₁ - p`, in two's complement.
  obtain ⟨r₂, hr₂⟩ : ∃ r₂, r₂ = r + (if r < 0 then p else 0) - p := ⟨_, rfl⟩
  have r₂lo : -p ≤ r₂ := by rw [hr₂]; split <;> omega
  have r₂hi : r₂ < p := by rw [hr₂]; split <;> omega
  have eR₂ : R₂ = r₂ + if r₂ < 0 then 2 * (A * 2 ^ 31) else 0 := by
    refine tc_eq hH (by omega) (by omega) hR₂0 (by rw [← hQ]; exact hR₂1) ?_
    have h1 : (R₂ + p) % (A * 2 ^ 32) = (r₂ + p) % (A * 2 ^ 32) := by
      rw [hR₂, eR₁, Int.emod_eq_of_lt (a := r₂ + p) (by omega) (by omega), hr₂]; ring
    rw [← hQ]; exact Int.ModEq.add_right_cancel' p h1
  have sR₂ := tc_neg (by omega) (by omega) eR₂
  -- `R₃ = norm p r`.
  have hc₂ : (if A * 2 ^ 31 ≤ R₂ then p else 0) = if r₂ < 0 then p else 0 := by simp only [sR₂]
  rw [hR₃, hc₂, eR₂, hQ]
  unfold mred norm
  rw [← hr]
  by_cases h2 : r₂ < 0
  · simp only [h2, ↓reduceIte]
    rw [show r₂ + 2 * (A * 2 ^ 31) + p = r₂ + p + 2 * (A * 2 ^ 31) * 1 by ring, Int.add_mul_emod_self_left,
      Int.emod_eq_of_lt (by omega) (by omega), hr₂]
    by_cases h : r < 0
    · simp only [h, ↓reduceIte]; ring
    · have h' : ¬ p ≤ r := by rw [hr₂] at h2; simp only [h, ↓reduceIte] at h2; omega
      simp only [h, h', ↓reduceIte]; ring
  · simp only [h2, ↓reduceIte, Int.add_zero]
    rw [Int.emod_eq_of_lt (by omega) (by omega), hr₂]
    by_cases h : r < 0
    · rw [hr₂] at h2; simp only [h, ↓reduceIte] at h2; omega
    · have h' : p ≤ r := by rw [hr₂] at h2; simp only [h, ↓reduceIte] at h2; omega
      simp only [h, h', ↓reduceIte]; ring

/-- `mred_words` on natural numbers, as words hold them (`B = 2^32`, `H = 2^31`). -/
theorem mred_nat {A B H p m W k E R R₁ R₂ R₃ : Nat} {t : Int} (hB : B = 2 ^ 32) (hH : H = 2 ^ 31) (hA : 0 < A)
    (hp : 0 < p) (hpA : p < A) (hm : (p * m + 1) % B = 0) (ht : |t| ≤ 2 ^ 31 * p)
    (hW1 : W < A * B) (hWt : (W : Int) % ((A * B : Nat) : Int) = t % ((A * B : Nat) : Int))
    (hk : k = W % B * m % B)
    (hE : E = (W + A * B * (if A * H ≤ W then B - 1 else 0) + k * p) % (A * B * B))
    (hR : R = E / B)
    (hR₁ : R₁ = (R + if A * H ≤ R then p else 0) % (A * B))
    (hR₂1 : R₂ < A * B) (hR₂ : (R₂ + p) % (A * B) = R₁)
    (hR₃ : R₃ = (R₂ + if A * H ≤ R₂ then p else 0) % (A * B)) :
    (R₃ : Int) = mred p m t := by
  have hB1 : 1 ≤ B := by rw [hB]; exact Nat.one_le_two_pow
  have hk1 : k < B := by rw [hk]; exact Nat.mod_lt _ (by omega)
  refine mred_words (A := A) (B := B) (H := H) (p := p) (m := m) (t := t) (W := W) (k := k) (E := E) (R := R)
    (R₁ := R₁) (R₂ := R₂) (R₃ := R₃) (by rw [hB]; norm_num) (by rw [hH]; norm_num) (by exact_mod_cast hA)
    (by exact_mod_cast hp) (by exact_mod_cast hpA) (by exact_mod_cast hm) ht (by omega) (by exact_mod_cast hW1)
    (by exact_mod_cast hWt) (by omega) (by exact_mod_cast hk1) ?_ ?_ ?_ ?_ (by omega) (by exact_mod_cast hR₂1) ?_ ?_
  · rw [hk]
    have h1 : W % B * m % B = W * m % B := by rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    rw [h1]; push_cast; rw [Int.emod_emod_of_dvd _ (dvd_refl _)]
  · rw [hE, ← Nat.cast_mul A H, ite_natCast_le]; push_cast [Nat.cast_sub hB1]; rfl
  · rw [hR]; push_cast; rfl
  · rw [hR₁, ← Nat.cast_mul A H, ite_natCast_le]; push_cast; rfl
  · rw [← hR₂]; push_cast; rfl
  · rw [hR₃, ← Nat.cast_mul A H, ite_natCast_le]; push_cast; rfl

end VG.Proof.Divstep.W32
