import VerifiedGarbage.Proof.Divstep.Tc32Words
import VerifiedGarbage.Proof.Divstep.Alg32Def

/-! # One-word signed Montgomery reduction -/
namespace VG.Proof.Divstep.W32

/-- `mredRaw` is exact: `2^32 · mredRaw t = t + k p`, with `k = t m mod 2^32`. -/
theorem mredRaw_spec {p m t : Int} (hm : (p * m + 1) % 2 ^ 32 = 0) :
    2 ^ 32 * mredRaw p m t = t + (t * m) % 2 ^ 32 * p := by
  unfold mredRaw
  apply Int.mul_ediv_cancel'
  -- `t + (t m mod 2^32) p ≡ t + t m p = t (1 + p m) ≡ 0`.
  have h1 : (2 : Int) ^ 32 ∣ p * m + 1 := Int.dvd_of_emod_eq_zero hm
  have h2 : (2 : Int) ^ 32 ∣ t * m - (t * m) % 2 ^ 32 := by
    have := Int.emod_add_ediv_mul (t * m) (2 ^ 32)
    exact ⟨(t * m) / 2 ^ 32, by linarith⟩
  have : t + (t * m) % 2 ^ 32 * p = t * (p * m + 1) - (t * m - (t * m) % 2 ^ 32) * p := by ring
  rw [this]
  exact dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_left h2 _)

/-- `2^32 mred t ≡ t` modulo `p`. -/
theorem mred_cong {p m t : Int} (hm : (p * m + 1) % 2 ^ 32 = 0) :
    2 ^ 32 * mred p m t ≡ t [ZMOD p] := by
  have hraw : 2 ^ 32 * mredRaw p m t ≡ t [ZMOD p] := by
    rw [mredRaw_spec hm]; exact Int.add_mul_emod_self_right _ _ _
  have hp0 : 2 ^ 32 * p ≡ 0 [ZMOD p] := Int.modEq_zero_iff_dvd.mpr (dvd_mul_left p _)
  unfold mred norm
  split
  · rw [mul_add]; simpa using hraw.add hp0
  · split
    · rw [mul_sub]; simpa using hraw.sub hp0
    · exact hraw

/-- `mred t` is in `[0, p)` for `|t| < 2^31 p` (with `0 ≤ k < 2^32`). -/
theorem mred_range {p m t : Int} (hp : 0 < p) (hm : (p * m + 1) % 2 ^ 32 = 0) (ht : |t| ≤ 2 ^ 31 * p) :
    0 ≤ mred p m t ∧ mred p m t < p := by
  have hraw := mredRaw_spec (t := t) hm
  have hk0 : 0 ≤ (t * m) % 2 ^ 32 := Int.emod_nonneg _ (by norm_num)
  have hk1 : (t * m) % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by norm_num)
  rw [abs_le] at ht
  -- `-p < mredRaw t < 2p`.
  have lo : -p < mredRaw p m t := by
    by_contra h; push Not at h
    have : 2 ^ 32 * mredRaw p m t ≤ 2 ^ 32 * (-p) := by nlinarith
    nlinarith
  have hi : mredRaw p m t < 2 * p := by
    by_contra h; push Not at h
    have : 2 ^ 32 * (2 * p) ≤ 2 ^ 32 * mredRaw p m t := by nlinarith
    nlinarith
  unfold mred norm
  split
  · constructor <;> linarith
  · split <;> constructor <;> linarith

end VG.Proof.Divstep.W32
