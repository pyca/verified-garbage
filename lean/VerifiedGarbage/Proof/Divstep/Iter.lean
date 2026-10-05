import VerifiedGarbage.Proof.Divstep.Bound

/-!
# The divstep and its bound

Bernstein–Yang's divstep in its "half-delta" form, as J. Harrison's
`idivstep` (HOL Light `Divstep/idivstep.ml`) and libsecp256k1's `divsteps`
iterate it: from `(d, f, g)` with `f` odd,
`(2 - d, g, (g - f)/2)` if `d ≥ 0` and `g` is odd, else
`(2 + d, f, (g + (g mod 2) f)/2)`, from `d = 1`. Its runs are runs of the
relaxed iteration for `i = (d - 1)/2` (`run`), so from `0 ≤ g ≤ f ≤ 2^256`,
`f` odd, `g` is zero after 590 steps (`g_590`), and `f` is then `± gcd(f, g)`
(`f_gcd`).
-/

namespace VG.Proof.Divstep

/-- One divstep on `(d, f, g)`. -/
def divstep (t : Int × Int × Int) : Int × Int × Int :=
  if 0 ≤ t.1 ∧ t.2.2 % 2 = 1 then (2 - t.1, t.2.2, (t.2.2 - t.2.1) / 2)
  else (2 + t.1, t.2.1, (t.2.2 + t.2.2 % 2 * t.2.1) / 2)

/-- `n` divsteps. -/
def divsteps : Nat → Int × Int × Int → Int × Int × Int
  | 0, t => t
  | n + 1, t => divsteps n (divstep t)

theorem divsteps_succ (n : Nat) (t : Int × Int × Int) : divsteps (n + 1) t = divstep (divsteps n t) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => rw [divsteps, ih, divsteps]

/-- The state after `n` steps: `d` odd, `f` odd. -/
theorem divsteps_odd {d f g : Int} (hd : d % 2 = 1) (hf : f % 2 = 1) :
    ∀ n, (divsteps n (d, f, g)).1 % 2 = 1 ∧ (divsteps n (d, f, g)).2.1 % 2 = 1
  | 0 => ⟨hd, hf⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := divsteps_odd hd hf n
    rw [divsteps_succ]
    generalize divsteps n (d, f, g) = t at h1 h2
    obtain ⟨d', f', g'⟩ := t
    simp only at h1 h2
    unfold divstep
    split
    · rename_i h; exact ⟨by omega, h.2⟩
    · exact ⟨by omega, h2⟩

/-- A zero `g` stays zero. -/
theorem divsteps_zero {t : Int × Int × Int} (h : t.2.2 = 0) : ∀ n, (divsteps n t).2.2 = 0 ∧ (divsteps n t).2.1 = t.2.1
  | 0 => ⟨h, rfl⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := divsteps_zero h n
    rw [divsteps_succ]
    generalize divsteps n t = u at h1 h2
    obtain ⟨d', f', g'⟩ := u
    simp only at h1 h2
    subst h1
    unfold divstep
    simp [h2]

theorem divsteps_add (n k : Nat) (t : Int × Int × Int) : divsteps (n + k) t = divsteps k (divsteps n t) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, divsteps_succ, divsteps_succ, ih]

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

theorem gcd_two {a : Int} (ha : a % 2 = 1) : Int.gcd a 2 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, a = 1 + k * 2 := ⟨a / 2, by omega⟩
  rw [Int.gcd_add_mul_right_left]; decide

/-- Halving with an odd other side keeps the gcd. -/
theorem gcd_half {a b : Int} (ha : a % 2 = 1) (hb : b % 2 = 0) : Int.gcd a (b / 2) = Int.gcd a b := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c * 2 := ⟨b / 2, by omega⟩
  rw [Int.mul_ediv_cancel _ (by decide), Int.gcd_mul_left_right_of_gcd_eq_one (gcd_two ha)]

/-- A divstep keeps `gcd(f, g)` (with `f` odd). -/
theorem divstep_gcd {d f g : Int} (hf : f % 2 = 1) :
    Int.gcd (divstep (d, f, g)).2.1 (divstep (d, f, g)).2.2 = Int.gcd f g := by
  unfold divstep
  simp only
  split
  · rename_i h
    rw [gcd_half h.2 (by omega), Int.gcd_self_sub_right, Int.gcd_comm]
  · rcases Int.emod_two_eq_zero_or_one g with hg | hg
    · rw [hg, zero_mul, add_zero, gcd_half hf hg]
    · rw [hg, one_mul, gcd_half hf (by omega)]
      have : g + f = g + 1 * f := by ring
      rw [this, Int.gcd_add_mul_right_right]

theorem divsteps_gcd {d f g : Int} (hd : d % 2 = 1) (hf : f % 2 = 1) :
    ∀ n, Int.gcd (divsteps n (d, f, g)).2.1 (divsteps n (d, f, g)).2.2 = Int.gcd f g
  | 0 => rfl
  | n + 1 => by
    rw [divsteps_succ]
    have hodd := (divsteps_odd (g := g) hd hf n).2
    have ih := divsteps_gcd (g := g) hd hf n
    generalize divsteps n (d, f, g) = t at hodd ih
    obtain ⟨d', f', g'⟩ := t
    rw [divstep_gcd hodd]; exact ih

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

/-- 576-bit moduli (nine words): 1328 divsteps. -/
theorem divsteps_1328 {f g : Int} (hf : f % 2 = 1) (hg : 0 ≤ g) (hgf : g ≤ f) (hf2 : f ≤ 2 ^ 576) {n : Nat}
    (hn : 1328 ≤ n) : (divsteps n (1, f, g)).2.2 = 0 ∧ (divsteps n (1, f, g)).2.1.natAbs = Int.gcd f g :=
  divsteps_bound hf hg hgf hf2 (pow_fuzz (by decide +kernel)) hn

end VG.Proof.Divstep
