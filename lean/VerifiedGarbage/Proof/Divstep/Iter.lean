import VerifiedGarbage.Proof.Divstep.Bound
import VerifiedGarbage.Proof.Divstep.Steps

/-!
# The divstep's bound

The divstep's (`Steps.lean`) runs are runs of the relaxed iteration for
`i = (d - 1)/2` (`run`), so from `0 ≤ g ≤ f ≤ 2^256`, `f` odd, `g` is zero
after 590 steps (`divsteps_590`; 885 up to `2^384`, `divsteps_words`), and
`f` is then `± gcd(f, g)`.
-/

namespace VG.Proof.Divstep

theorem ediv2_cast {a : Int} (h : a % 2 = 0) : ((a / 2 : Int) : ℚ) = (a : ℚ) / 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
  rw [Int.mul_ediv_cancel_left _ (by decide)]; push_cast; ring

/-- The divstep's runs are runs of the relaxed iteration, with `i = (d - 1)/2`. -/
theorem run {f g : Int} (hf : f % 2 = 1) :
    Run (fun n => ((divsteps n (1, f, g)).1 - 1) / 2) (fun n => ((divsteps n (1, f, g)).2.1 : ℚ))
      (fun n => ((divsteps n (1, f, g)).2.2 : ℚ)) := by
  refine ⟨by simp [divsteps], fun n => ?_⟩
  obtain ⟨hd, hf'⟩ := divsteps_odd (d := 1) (g := g) (by decide) hf n
  simp only [divsteps_succ]
  generalize divsteps n (1, f, g) = t at hd hf'
  obtain ⟨d, f', g'⟩ := t
  simp only at hd hf' ⊢
  unfold divstep Step
  simp only
  split
  · rename_i h
    obtain ⟨hd0, hg⟩ := h
    right
    rw [ite_f (by omega)]
    refine ⟨by omega, rfl, ?_⟩
    simp only; rw [ediv2_cast (a := g' - f') (by omega)]; push_cast; ring
  · rename_i h
    rcases Int.emod_two_eq_zero_or_one g' with hg | hg
    · left
      refine ⟨by omega, rfl, ?_⟩
      simp only [hg, zero_mul, add_zero]; exact ediv2_cast hg
    · right
      rw [ite_t (by omega)]
      refine ⟨by omega, rfl, ?_⟩
      simp only [hg, one_mul]; rw [ediv2_cast (by omega)]; push_cast; ring

/-- `2^b s^m` is at most the fuzziness, in naturals. -/
theorem pow_fuzz {b m : Nat} (h : 2 ^ b * sn ^ m * 8388608 ≤ 8388391 * sd ^ m) : (2 : ℚ) ^ b * s ^ m ≤ fuzz := by
  have hq : ((2 ^ b * sn ^ m * 8388608 : Nat) : ℚ) ≤ ((8388391 * sd ^ m : Nat) : ℚ) := by exact_mod_cast h
  push_cast at hq
  rw [s_pow, fuzz, mul_div_assoc', div_le_div_iff₀ (by unfold sd; positivity) (by norm_num)]
  linarith

/-- From `0 ≤ g ≤ f ≤ 2^b`, `f` odd, `g` is zero after any `n ≥ m` divsteps if
`2^b s^m` is at most the fuzziness. -/
theorem g_bound {f g : Int} (hf : f % 2 = 1) (hg : 0 ≤ g) (hgf : g ≤ f) {b m : Nat} (hf2 : f ≤ 2 ^ b)
    (hbm : (2 : ℚ) ^ b * s ^ m ≤ fuzz) {n : Nat} (hn : m ≤ n) : (divsteps n (1, f, g)).2.2 = 0 := by
  obtain ⟨k, hk, h0⟩ := endToEnd (run (g := g) hf) (fun n => ⟨_, rfl⟩) (fun n => ⟨_, rfl⟩)
    (M := 2 ^ b) (m := m) (by simp [divsteps]; exact_mod_cast hg)
    (by simp [divsteps]; exact_mod_cast hgf) (by simp [divsteps]; exact_mod_cast hf2) hbm
  simp only [Int.cast_eq_zero] at h0
  obtain ⟨j, rfl⟩ : ∃ j, n = k + j := ⟨n - k, by omega⟩
  rw [divsteps_add]
  exact (divsteps_zero h0 j).1

/-- From `0 ≤ g ≤ f ≤ 2^b`, `f` odd, after any `n ≥ m` divsteps `g` is zero
and `|f| = gcd(f, g)`, if `2^b s^m` is at most the fuzziness. -/
theorem divsteps_bound {f g : Int} (hf : f % 2 = 1) (hg : 0 ≤ g) (hgf : g ≤ f) {b m : Nat} (hf2 : f ≤ 2 ^ b)
    (hbm : (2 : ℚ) ^ b * s ^ m ≤ fuzz) {n : Nat} (hn : m ≤ n) :
    (divsteps n (1, f, g)).2.2 = 0 ∧ (divsteps n (1, f, g)).2.1.natAbs = Int.gcd f g := by
  have h0 := g_bound hf hg hgf hf2 hbm hn
  refine ⟨h0, ?_⟩
  have := divsteps_gcd (d := 1) (g := g) (by decide) hf n
  rw [h0, Int.gcd_zero_right] at this
  exact this

/-- 256-bit moduli: 590 divsteps (`9437 b + 1 ≤ 4096 m`). -/
theorem divsteps_590 {f g : Int} (hf : f % 2 = 1) (hg : 0 ≤ g) (hgf : g ≤ f) (hf2 : f ≤ 2 ^ 256) {n : Nat}
    (hn : 590 ≤ n) : (divsteps n (1, f, g)).2.2 = 0 ∧ (divsteps n (1, f, g)).2.1.natAbs = Int.gcd f g :=
  divsteps_bound hf hg hgf hf2 (pow_fuzz (by decide +kernel)) hn

/-- 384-bit moduli: 885 divsteps. -/
theorem divsteps_885 {f g : Int} (hf : f % 2 = 1) (hg : 0 ≤ g) (hgf : g ≤ f) (hf2 : f ≤ 2 ^ 384) {n : Nat}
    (hn : 885 ≤ n) : (divsteps n (1, f, g)).2.2 = 0 ∧ (divsteps n (1, f, g)).2.1.natAbs = Int.gcd f g :=
  divsteps_bound hf hg hgf hf2 (pow_fuzz (by decide +kernel)) hn

/-- Enough divsteps for numbers of `n` words: `590` for `n ≤ 4` (256 bits),
`885` for `n ≤ 6` (384). -/
theorem divsteps_words {f g : Int} {n N : Nat} (hf : f % 2 = 1) (hg : 0 ≤ g) (hgf : g ≤ f)
    (hfn : f < 2 ^ (64 * n)) (hb : (n ≤ 4 ∧ 590 ≤ N) ∨ (n ≤ 6 ∧ 885 ≤ N)) :
    (divsteps N (1, f, g)).2.2 = 0 ∧ (divsteps N (1, f, g)).2.1.natAbs = Int.gcd f g := by
  rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine divsteps_590 hf hg hgf ?_ h2
    calc f ≤ 2 ^ (64 * n) := hfn.le
      _ ≤ 2 ^ 256 := pow_le_pow_right₀ (by norm_num) (by omega)
  · refine divsteps_885 hf hg hgf ?_ h2
    calc f ≤ 2 ^ (64 * n) := hfn.le
      _ ≤ 2 ^ 384 := pow_le_pow_right₀ (by norm_num) (by omega)

end VG.Proof.Divstep
