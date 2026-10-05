import VerifiedGarbage.Proof.Divstep.Iter
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

/-- A divstep state and its transition matrix. -/
structure MSt where
  d : Int
  f : Int
  g : Int
  u : Int
  v : Int
  q : Int
  r : Int

/-- A divstep, with the matrix doubled and combined as `(f, g)` are. -/
def mstep (t : MSt) : MSt :=
  if 0 ≤ t.d ∧ t.g % 2 = 1 then ⟨2 - t.d, t.g, (t.g - t.f) / 2, 2 * t.q, 2 * t.r, t.q - t.u, t.r - t.v⟩
  else ⟨2 + t.d, t.f, (t.g + t.g % 2 * t.f) / 2, 2 * t.u, 2 * t.v, t.q + t.g % 2 * t.u, t.r + t.g % 2 * t.v⟩

/-- `n` such steps. -/
def msteps : Nat → MSt → MSt
  | 0, t => t
  | n + 1, t => msteps n (mstep t)

/-- The start of a batch: `(d, f, g)` and the identity. -/
def MSt.init (d f g : Int) : MSt := ⟨d, f, g, 1, 0, 0, 1⟩

theorem msteps_succ (n : Nat) (t : MSt) : msteps (n + 1) t = mstep (msteps n t) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => rw [msteps, ih, msteps]

/-- The state is `divsteps`'. -/
theorem msteps_dfg (n : Nat) (t : MSt) :
    ((msteps n t).d, (msteps n t).f, (msteps n t).g) = divsteps n (t.d, t.f, t.g) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [msteps, ih, divsteps]
    congr 1
    unfold mstep divstep
    split <;> rfl

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
    · rw [pow_succ]; linear_combination 2 * h2
    · rw [pow_succ, mul_assoc, e]; linear_combination h2 - h1
  · rename_i hc
    simp only
    rcases Int.emod_two_eq_zero_or_one t.g with hg | hg
    · rw [hg]
      have e : 2 * ((t.g + 0 * t.f) / 2) = t.g := by rw [zero_mul, add_zero]; exact Int.mul_ediv_cancel' (by omega)
      constructor
      · rw [pow_succ]; linear_combination 2 * h1
      · rw [pow_succ, mul_assoc, e]; linear_combination h2
    · rw [hg]
      have e : 2 * ((t.g + 1 * t.f) / 2) = t.g + t.f := by rw [one_mul]; exact Int.mul_ediv_cancel' (by omega)
      constructor
      · rw [pow_succ]; linear_combination 2 * h1
      · rw [pow_succ, mul_assoc, e]; linear_combination h2 + h1

/-- `f` stays odd. -/
theorem mstep_f_odd {t : MSt} (hf : t.f % 2 = 1) : (mstep t).f % 2 = 1 := by
  unfold mstep; split
  · rename_i h; exact h.2
  · exact hf

theorem msteps_f_odd {t : MSt} (hf : t.f % 2 = 1) : ∀ n, (msteps n t).f % 2 = 1
  | 0 => hf
  | n + 1 => by rw [msteps_succ]; exact mstep_f_odd (msteps_f_odd hf n)

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
  have hg := Int.emod_two_eq_zero_or_one t.g
  unfold mstep MSt.bnd
  rw [pow_succ]
  split
  · simp only
    refine ⟨?_, ?_⟩
    · rw [abs_mul, abs_mul]; norm_num; linarith
    · have := abs_sub t.q t.u; have := abs_sub t.r t.v; linarith
  · simp only
    refine ⟨?_, ?_⟩
    · rw [abs_mul, abs_mul]; norm_num; linarith
    · have := abs_add_le t.q (t.g % 2 * t.u); have := abs_add_le t.r (t.g % 2 * t.v)
      have := hb _ hg t.u; have := hb _ hg t.v; linarith

theorem msteps_bnd (d f g : Int) : ∀ n, (msteps n (MSt.init d f g)).bnd n
  | 0 => by simp [MSt.bnd, MSt.init, msteps]
  | n + 1 => by rw [msteps_succ]; exact mstep_bnd (msteps_bnd d f g n)

/-- `|d|` grows by at most 2 a step. -/
theorem mstep_d (t : MSt) : |(mstep t).d| ≤ |t.d| + 2 := by
  unfold mstep; split <;> simp only <;> rw [abs_le] <;> constructor <;>
    linarith [abs_nonneg t.d, le_abs_self t.d, neg_abs_le t.d]

theorem msteps_d (t : MSt) : ∀ n, |(msteps n t).d| ≤ |t.d| + 2 * n
  | 0 => by simp [msteps]
  | n + 1 => by
    rw [msteps_succ]
    have := mstep_d (msteps n t)
    have := msteps_d t n
    push_cast; linarith

/-- States with the same `d` and matrix, and `f`, `g` congruent modulo `2^k`. -/
def MSt.cong (t t' : MSt) (k : Nat) : Prop :=
  t.d = t'.d ∧ t.u = t'.u ∧ t.v = t'.v ∧ t.q = t'.q ∧ t.r = t'.r ∧
    t.f % 2 ^ k = t'.f % 2 ^ k ∧ t.g % 2 ^ k = t'.g % 2 ^ k

/-- Halving congruent even numbers. -/
theorem half_cong {a a' : Int} {k : Nat} (h : a % 2 ^ (k + 1) = a' % 2 ^ (k + 1)) (ha : a % 2 = 0)
    (ha' : a' % 2 = 0) : (a / 2) % 2 ^ k = (a' / 2) % 2 ^ k := by
  have h2k : (0 : Int) < 2 ^ k := by positivity
  obtain ⟨c, hc⟩ : (2 ^ (k + 1) : Int) ∣ a' - a := Int.ModEq.dvd h
  have e1 : a = 2 * (a / 2) := (Int.mul_ediv_cancel' (by omega)).symm
  have e2 : a' = 2 * (a' / 2) := (Int.mul_ediv_cancel' (by omega)).symm
  have : a' / 2 - a / 2 = 2 ^ k * c := by
    have : 2 * (a' / 2 - a / 2) = 2 * (2 ^ k * c) := by rw [pow_succ] at hc; linarith
    exact mul_left_cancel₀ (by norm_num) this
  exact Int.modEq_of_dvd ⟨c, this⟩

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
