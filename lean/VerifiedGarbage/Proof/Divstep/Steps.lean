import VerifiedGarbage.Proof.Framework.PowLit

/-!
# The divstep

Bernstein–Yang's divstep in its "half-delta" form, as J. Harrison's
`idivstep` (HOL Light `Divstep/idivstep.ml`) and libsecp256k1's `divsteps`
iterate it: from `(d, f, g)` with `f` odd,
`(2 - d, g, (g - f)/2)` if `d ≥ 0` and `g` is odd, else
`(2 + d, f, (g + (g mod 2) f)/2)`, from `d = 1`. It keeps `d` and `f` odd
(`divsteps_odd`) and `gcd(f, g)` (`divsteps_gcd`); `Iter.lean` bounds the
steps until `g` is zero.
-/

namespace VG.Proof.Divstep

theorem ite_t {α : Sort _} {c : Prop} [Decidable c] (h : c) {x y : α} : (if c then x else y) = x := by
  simp [h]

theorem ite_f {α : Sort _} {c : Prop} [Decidable c] (h : ¬c) {x y : α} : (if c then x else y) = y := by
  simp [h]

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
  · rcases (by omega : g % 2 = 0 ∨ g % 2 = 1) with hg | hg
    · rw [hg, Int.zero_mul, Int.add_zero, gcd_half hf hg]
    · rw [hg, Int.one_mul, gcd_half hf (by omega)]
      have : g + f = g + 1 * f := by rw [Int.one_mul]
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

end VG.Proof.Divstep
