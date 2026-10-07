import VerifiedGarbage.Proof.Divstep.Alg32
import VerifiedGarbage.Proof.Divstep.Tc32Red

/-!
# Inversion by batches of divsteps: words in two's complement

A signed number in `[-H, H)` is held in `[0, 2H)` as itself, or plus `2H`
if negative (`tc_eq`); the reduction `mred` on such words, as the code does
it (`mred_words`): sign-extend `t` by a word, add `k p`, take the words above
the lowest, add `p` if negative, subtract `p`, and add `p` back if negative.
-/

namespace VG.Proof.Divstep.W32

/-- A divstep keeps `|f|, |g| ≤ M` (from an odd `f`). -/
theorem divstep_le {M : Int} {t : Int × Int × Int} (hf : t.2.1 % 2 = 1) (h1 : |t.2.1| ≤ M) (h2 : |t.2.2| ≤ M) :
    |(divstep t).2.1| ≤ M ∧ |(divstep t).2.2| ≤ M := by
  obtain ⟨d, f, g⟩ := t
  simp only at hf h1 h2
  rw [abs_le] at h1 h2
  unfold divstep
  split
  · rename_i h
    simp only at h ⊢
    refine ⟨abs_le.mpr h2, abs_le.mpr ⟨?_, ?_⟩⟩ <;> omega
  · simp only
    refine ⟨abs_le.mpr h1, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
    · rcases Int.emod_two_eq_zero_or_one g with hg | hg <;> rw [hg] <;> omega

theorem divsteps_le {M d f g : Int} (hd : d % 2 = 1) (hf : f % 2 = 1) (h1 : |f| ≤ M) (h2 : |g| ≤ M) :
    ∀ n, |(divsteps n (d, f, g)).2.1| ≤ M ∧ |(divsteps n (d, f, g)).2.2| ≤ M
  | 0 => ⟨h1, h2⟩
  | n + 1 => by
    obtain ⟨a, b⟩ := divsteps_le hd hf h1 h2 n
    rw [divsteps_succ]
    exact divstep_le (divsteps_odd hd hf n).2 a b

theorem divstep_d (t : Int × Int × Int) : |(divstep t).1| ≤ |t.1| + 2 := by
  unfold divstep
  split <;> simp only <;> rw [abs_le] <;> constructor <;>
    linarith [abs_nonneg t.1, le_abs_self t.1, neg_abs_le t.1]

theorem divsteps_d (t : Int × Int × Int) : ∀ n, |(divsteps n t).1| ≤ |t.1| + 2 * n
  | 0 => by simp [divsteps]
  | n + 1 => by
    rw [divsteps_succ]
    have := divstep_d (divsteps n t)
    have := divsteps_d t n
    push_cast; linarith

/-- The state after `B` batches is bounded: `|d| ≤ 1 + 2 N B`, `f` odd, `|f|, |g| ≤ p`,
`a`, `b` in `[0, p)`. -/
theorem invRun_bounds {N : Nat} (hN : N ≤ 30) {p m x : Int} (hp : p % 2 = 1) (hp1 : 1 < p)
    (hm : (p * m + 1) % 2 ^ 32 = 0) (hx0 : 0 ≤ x) (hxp : x < p) (B : Nat) :
    |(invRun N p m x B).d| ≤ 1 + 2 * (N * B : Nat) ∧ (invRun N p m x B).f % 2 = 1 ∧
      |(invRun N p m x B).f| ≤ p ∧ |(invRun N p m x B).g| ≤ p ∧
      0 ≤ (invRun N p m x B).a ∧ (invRun N p m x B).a < p ∧ 0 ≤ (invRun N p m x B).b ∧ (invRun N p m x B).b < p := by
  obtain ⟨hd, hodd⟩ := invRun_dfg (N := N) (m := m) (x := x) hp B
  obtain ⟨-, -, a0, a1, b0, b1⟩ := invRun_inv (x := x) hN hp hp1 hm B
  have e1 : (invRun N p m x B).d = (divsteps (N * B) (1, p, x)).1 := by rw [← hd]
  have e2 : (invRun N p m x B).f = (divsteps (N * B) (1, p, x)).2.1 := by rw [← hd]
  have e3 : (invRun N p m x B).g = (divsteps (N * B) (1, p, x)).2.2 := by rw [← hd]
  obtain ⟨lf, lg⟩ := divsteps_le (M := p) (d := 1) (f := p) (g := x) (by decide) hp
    (by rw [abs_of_pos (by omega)]) (by rw [abs_of_nonneg hx0]; omega) (N * B)
  have ld := divsteps_d (1, p, x) (N * B)
  refine ⟨?_, hodd, by rw [e2]; exact lf, by rw [e3]; exact lg, a0, a1, b0, b1⟩
  rw [e1]; simpa using ld

/-- `n` steps from `g = 0`: `g` stays `0`, `u`, `v` double. -/
theorem msteps_g0 : ∀ (n : Nat) (d f u v q r : Int),
    msteps n ⟨d, f, 0, u, v, q, r⟩ = ⟨d + 2 * n, f, 0, 2 ^ n * u, 2 ^ n * v, q, r⟩
  | 0, d, f, u, v, q, r => by simp [msteps]
  | n + 1, d, f, u, v, q, r => by
    rw [msteps]
    have : mstep ⟨d, f, 0, u, v, q, r⟩ = ⟨2 + d, f, 0, 2 * u, 2 * v, q, r⟩ := by
      simp [mstep]
    rw [this, msteps_g0 n]
    simp only [MSt.mk.injEq]
    refine ⟨by push_cast; ring, trivial, trivial, by ring, by ring, trivial, trivial⟩

/-- From `x = 0`, `g` and `a` stay `0`. -/
theorem invRun_zero {N : Nat} {p m : Int} (hp : 0 < p) :
    ∀ B, (invRun N p m 0 B).g = 0 ∧ (invRun N p m 0 B).a = 0
  | 0 => ⟨rfl, rfl⟩
  | B + 1 => by
    obtain ⟨hg, ha⟩ := invRun_zero hp B
    simp only [invRun, batch]
    generalize invRun N p m 0 B = s at hg ha
    obtain ⟨d, f, g, a, b⟩ := s
    simp only at hg ha
    subst hg ha
    rw [MSt.init, msteps_g0]
    simp only [mul_zero, add_zero, zero_add, mul_one]
    simp [mred, mredRaw, norm, show ¬ p ≤ 0 by omega]

end VG.Proof.Divstep.W32
