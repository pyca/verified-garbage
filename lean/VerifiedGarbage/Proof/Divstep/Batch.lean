import VerifiedGarbage.Proof.Divstep.BatchBasic
import Mathlib.Data.Int.ModEq

/-!
# Divsteps in batches

The divstep with its transition matrix (`mstep`, as J. Harrison's
`divstep_mat`): from the identity, `n` steps give `(d, f, g)` of `divsteps`
(`msteps_dfg`) and `(u, v, q, r)` with `2^n f_n = u f + v g`,
`2^n g_n = q f + r g` (`msteps_mat`), entries at most `2^n` (`msteps_bound`).
They read only `d` and `g mod 2`, so `n` steps on `f`, `g` taken modulo
`2^N` (`n ≤ N`) give the same `d` and matrix (`msteps_cong`): a batch runs on
the low words and its matrix updates the whole numbers.
-/

namespace VG.Proof.Divstep

/-- The matrix: `2^k f = u f₀ + v g₀`, `2^k g = q f₀ + r g₀` is kept, with `k + 1`,
by a step from an odd `f`. -/
def MSt.rel (t : MSt) (k : Nat) (f₀ g₀ : Int) : Prop :=
  2 ^ k * t.f = t.u * f₀ + t.v * g₀ ∧ 2 ^ k * t.g = t.q * f₀ + t.r * g₀

theorem mstep_rel {t : MSt} {k : Nat} {f₀ g₀ : Int} (hf : t.f % 2 = 1) (h : t.rel k f₀ g₀) :
    (mstep t).rel (k + 1) f₀ g₀ := by
  obtain ⟨h1, h2⟩ := h
  unfold mstep MSt.rel
  split
  · rename_i hc
    simp only
    have e : 2 * ((t.g - t.f) / 2) = t.g - t.f := Int.mul_ediv_cancel' (by omega)
    constructor
    · rw [pow_succ]; rw [mul_right_comm, h2, add_mul]; simp only [mul_assoc, mul_comm]
    · rw [pow_succ, mul_assoc, e]; rw [mul_sub, h2, h1]; simp only [sub_mul]; omega
  · rename_i hc
    simp only
    rcases Int.emod_two_eq_zero_or_one t.g with hg | hg
    · rw [hg]
      have e : 2 * ((t.g + 0 * t.f) / 2) = t.g := by rw [zero_mul, add_zero]; exact Int.mul_ediv_cancel' (by omega)
      constructor
      · rw [pow_succ]; rw [mul_right_comm, h1, add_mul]; simp only [mul_assoc, mul_comm]
      · rw [pow_succ, mul_assoc, e]; simpa using h2
    · rw [hg]
      have e : 2 * ((t.g + 1 * t.f) / 2) = t.g + t.f := by rw [one_mul]; exact Int.mul_ediv_cancel' (by omega)
      constructor
      · rw [pow_succ]; rw [mul_right_comm, h1, add_mul]; simp only [mul_assoc, mul_comm]
      · rw [pow_succ, mul_assoc, e]; rw [mul_add, h2, h1]; simp only [add_mul, one_mul]; omega

/-- `n` steps from the identity: `2^n f_n = u f + v g`, `2^n g_n = q f + r g`. -/
theorem msteps_mat {d f g : Int} (hf : f % 2 = 1) (n : Nat) :
    (msteps n (MSt.init d f g)).rel n f g := by
  induction n with
  | zero => simp [MSt.rel, MSt.init, msteps]
  | succ n ih =>
    rw [msteps_succ]
    exact mstep_rel (msteps_f_odd (t := MSt.init d f g) hf n) ih

/-- The matrix's rows have `|u| + |v| ≤ 2^n` and `|q| + |r| ≤ 2^n` after `n` steps
from the identity. -/
def MSt.bnd (t : MSt) (n : Nat) : Prop := |t.u| + |t.v| ≤ 2 ^ n ∧ |t.q| + |t.r| ≤ 2 ^ n

theorem mstep_bnd {t : MSt} {n : Nat} (h : t.bnd n) : (mstep t).bnd (n + 1) := by
  obtain ⟨h1, h2⟩ := h
  have hb : ∀ b : Int, (b = 0 ∨ b = 1) → ∀ x : Int, |b * x| ≤ |x| := fun b hb x => by
    rcases hb with rfl | rfl <;> simp
  have twice (x : Int) : |2*x| = 2*|x| := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx, abs_of_nonneg (by omega)]
    · rw [abs_of_neg (by omega : x < 0), abs_of_neg (by omega : 2*x < 0)]; omega
  have hg := Int.emod_two_eq_zero_or_one t.g
  unfold mstep MSt.bnd
  rw [pow_succ]
  split
  · simp only
    refine ⟨?_, ?_⟩
    · rw [twice, twice]; omega
    · have hq := abs_add_le t.q (-t.u); have hr := abs_add_le t.r (-t.v)
      simp only [← sub_eq_add_neg, abs_neg] at hq hr; omega
  · simp only
    refine ⟨?_, ?_⟩
    · rw [twice, twice]; omega
    · have := abs_add_le t.q (t.g % 2 * t.u); have := abs_add_le t.r (t.g % 2 * t.v)
      have := hb _ hg t.u; have := hb _ hg t.v; omega

theorem msteps_bnd (d f g : Int) : ∀ n, (msteps n (MSt.init d f g)).bnd n
  | 0 => by simp only [MSt.bnd, MSt.init, msteps]; decide
  | n + 1 => by rw [msteps_succ]; exact mstep_bnd (msteps_bnd d f g n)

/-- States with the same `d` and matrix, and `f`, `g` congruent modulo `2^k`. -/
def MSt.cong (t t' : MSt) (k : Nat) : Prop :=
  t.d = t'.d ∧ t.u = t'.u ∧ t.v = t'.v ∧ t.q = t'.q ∧ t.r = t'.r ∧
    t.f % 2 ^ k = t'.f % 2 ^ k ∧ t.g % 2 ^ k = t'.g % 2 ^ k

theorem mstep_cong {t t' : MSt} {k : Nat} (ht : t.f % 2 = 1) (h : t.cong t' (k + 1)) :
    (mstep t).cong (mstep t') k := by
  obtain ⟨hd, hu, hv, hq, hr, hf, hg⟩ := h
  -- `g mod 2` and `f mod 2` agree.
  have hg2 : t.g % 2 = t'.g % 2 := by
    have := congrArg (· % 2) hg
    simp only [Int.emod_emod_of_dvd _ (show (2 : Int) ∣ 2 ^ (k + 1) by
      exact dvd_pow_self 2 (by omega))] at this
    exact this
  have hf2 : t.f % 2 = t'.f % 2 := by
    have := congrArg (· % 2) hf
    simp only [Int.emod_emod_of_dvd _ (show (2 : Int) ∣ 2 ^ (k + 1) by
      exact dvd_pow_self 2 (by omega))] at this
    exact this
  have hk : (2 : Int) ^ k ∣ 2 ^ (k + 1) := pow_dvd_pow 2 (by omega)
  have hfk : t.f % 2 ^ k = t'.f % 2 ^ k := by
    rw [← Int.emod_emod_of_dvd t.f hk, ← Int.emod_emod_of_dvd t'.f hk, hf]
  unfold mstep MSt.cong
  rw [hd, hg2]
  split
  · rename_i hc
    refine ⟨rfl, by rw [hq], by rw [hr], by rw [hq, hu], by rw [hr, hv], ?_, ?_⟩
    · rw [← Int.emod_emod_of_dvd t.g hk, ← Int.emod_emod_of_dvd t'.g hk, hg]
    · refine half_cong ?_ (by omega) (by omega)
      rw [Int.sub_emod, hg, hf, ← Int.sub_emod]
  · refine ⟨rfl, by rw [hu], by rw [hv], by rw [hq, hu], by rw [hr, hv], hfk, ?_⟩
    rcases Int.emod_two_eq_zero_or_one t'.g with h0 | h0
    · simp only [h0, zero_mul, add_zero]
      exact half_cong hg (by omega) (by omega)
    · simp only [h0, one_mul]
      refine half_cong ?_ (by omega) (by omega)
      rw [Int.add_emod, hg, hf, ← Int.add_emod]

/-- `n ≤ N` steps on `f`, `g` modulo `2^N` give the same `d` and matrix. -/
theorem msteps_cong {t t' : MSt} {N : Nat} (ht : t.f % 2 = 1) (h : t.cong t' N) :
    ∀ n ≤ N, (msteps n t).cong (msteps n t') (N - n)
  | 0, _ => by simpa [msteps] using h
  | n + 1, hn => by
    rw [msteps_succ, msteps_succ]
    have := msteps_cong ht h n (by omega)
    rw [show N - n = (N - (n + 1)) + 1 by omega] at this
    exact mstep_cong (msteps_f_odd ht n) this

end VG.Proof.Divstep
