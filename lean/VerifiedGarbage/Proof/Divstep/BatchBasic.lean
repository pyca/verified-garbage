import VerifiedGarbage.Proof.Divstep.Steps
import Mathlib.Data.Int.ModEq

/-! # Divstep matrices and their scalar state -/
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

/-- `f` stays odd. -/
theorem mstep_f_odd {t : MSt} (hf : t.f % 2 = 1) : (mstep t).f % 2 = 1 := by
  unfold mstep; split
  · rename_i h; exact h.2
  · exact hf

theorem msteps_f_odd {t : MSt} (hf : t.f % 2 = 1) : ∀ n, (msteps n t).f % 2 = 1
  | 0 => hf
  | n + 1 => by rw [msteps_succ]; exact mstep_f_odd (msteps_f_odd hf n)

theorem mstep_d (t : MSt) : |(mstep t).d| ≤ |t.d| + 2 := by
  have := abs_nonneg t.d
  have := le_abs_self t.d
  have := neg_abs_le t.d
  unfold mstep; split <;> simp only <;> rw [abs_le'] <;> constructor <;>
    omega

theorem msteps_d (t : MSt) : ∀ n, |(msteps n t).d| ≤ |t.d| + 2 * n
  | 0 => by simp [msteps]
  | n + 1 => by
    rw [msteps_succ]
    have := mstep_d (msteps n t)
    have := msteps_d t n
    simp only [Nat.cast_add, Nat.cast_one]
    omega

/-- Halving congruent even numbers. -/
theorem half_cong {a a' : Int} {k : Nat} (h : a % 2 ^ (k + 1) = a' % 2 ^ (k + 1)) (ha : a % 2 = 0)
    (ha' : a' % 2 = 0) : (a / 2) % 2 ^ k = (a' / 2) % 2 ^ k := by
  obtain ⟨c, hc⟩ : (2 ^ (k + 1) : Int) ∣ a' - a := Int.ModEq.dvd h
  have hc' : a' - a = 2 * (2 ^ k * c) := by
    rw [hc, pow_succ, mul_assoc, mul_left_comm]
  have E : a' / 2 - a / 2 = 2 ^ k * c := by omega
  exact Int.modEq_of_dvd ⟨c, E⟩

end VG.Proof.Divstep
