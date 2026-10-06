import Mathlib.Data.Nat.GCD.Basic

/-!
# A binary gcd in a fixed number of steps

`gcdStep (u, v)` with `v` odd: if `u` is odd, `(|u − v| / 2, min u v)`, else
`(u / 2, v)`. It keeps `v` odd and `gcd u v`, and halves `u v` unless `u` is
zero, which stays zero; so from `u v < 2^n`, `n` steps end at
`(0, gcd u v)` (`gcdIter_eq`). The implementations run the steps on words
with masks, so that the number of steps does not depend on `u` or `v`.
-/

namespace VG.Proof.RsaKeyGen

/-- One step of the binary gcd. -/
def gcdStep (u v : Nat) : Nat × Nat :=
  if u % 2 = 1 then (if u < v then ((v - u) / 2, u) else ((u - v) / 2, v)) else (u / 2, v)

/-- `n` steps. -/
def gcdIter : Nat → Nat → Nat → Nat × Nat
  | 0, u, v => (u, v)
  | n + 1, u, v => gcdIter n (gcdStep u v).1 (gcdStep u v).2

theorem gcd_half {x u : Nat} (hx : x % 2 = 0) (hu : u % 2 = 1) : Nat.gcd (x / 2) u = Nat.gcd x u := by
  have hc : Nat.Coprime 2 u := by
    show Nat.gcd 2 u = 1
    rw [Nat.gcd_rec, hu]; rfl
  conv_rhs => rw [show x = 2 * (x / 2) by omega]
  exact (Nat.Coprime.gcd_mul_left_cancel _ hc).symm

theorem gcdStep_odd {u v : Nat} (hv : v % 2 = 1) : (gcdStep u v).2 % 2 = 1 := by
  unfold gcdStep; split
  · split <;> with_reducible assumption
  · exact hv

theorem gcdStep_gcd {u v : Nat} (hv : v % 2 = 1) :
    Nat.gcd (gcdStep u v).1 (gcdStep u v).2 = Nat.gcd u v := by
  unfold gcdStep
  split
  · rename_i hu
    split
    · rename_i h
      simp only
      rw [gcd_half (by omega) hu, Nat.gcd_comm, Nat.gcd_sub_self_right (by omega)]
    · rename_i h
      simp only
      rw [gcd_half (by omega) hv, Nat.gcd_sub_self_left (by omega)]
  · exact gcd_half (by omega) hv

theorem gcdStep_zero (v : Nat) : gcdStep 0 v = (0, v) := by simp [gcdStep]

theorem gcdStep_pot (u v : Nat) :
    2 * ((gcdStep u v).1 * (gcdStep u v).2) ≤ u * v := by
  unfold gcdStep
  split
  · split
    · rename_i h1 h2
      simp only
      have : 2 * ((v - u) / 2) ≤ v := by omega
      calc 2 * ((v - u) / 2 * u) = (2 * ((v - u) / 2)) * u := by rw [Nat.mul_assoc]
        _ ≤ v * u := Nat.mul_le_mul_right _ this
        _ = u * v := Nat.mul_comm _ _
    · simp only
      have : 2 * ((u - v) / 2) ≤ u := by omega
      calc 2 * ((u - v) / 2 * v) = (2 * ((u - v) / 2)) * v := by rw [Nat.mul_assoc]
        _ ≤ u * v := Nat.mul_le_mul_right _ this
  · simp only
    have : 2 * (u / 2) ≤ u := by omega
    calc 2 * (u / 2 * v) = (2 * (u / 2)) * v := by rw [Nat.mul_assoc]
      _ ≤ u * v := Nat.mul_le_mul_right _ this

theorem gcdIter_zero (v : Nat) : ∀ n, gcdIter n 0 v = (0, v)
  | 0 => rfl
  | n + 1 => by rw [gcdIter, gcdStep_zero]; exact gcdIter_zero v n

/-- `n` steps from `u v < 2^n`, `v` odd: `(0, gcd u v)`. -/
theorem gcdIter_eq : ∀ n u v, v % 2 = 1 → u * v < 2 ^ n → gcdIter n u v = (0, Nat.gcd u v)
  | 0, u, v, _, h => by
    have : u * v = 0 := by rw [Nat.pow_zero] at h; omega
    rcases Nat.mul_eq_zero.mp this with rfl | rfl
    · simp [gcdIter]
    · omega
  | n + 1, u, v, hv, h => by
    rw [gcdIter]
    by_cases hu : u = 0
    · subst hu; rw [gcdStep_zero, gcdIter_zero, Nat.gcd_zero_left]
    · rw [gcdIter_eq n _ _ (gcdStep_odd hv) (by have := gcdStep_pot u v; rw [Nat.pow_succ] at h; omega),
        gcdStep_gcd hv]

/-- One more step, last. -/
theorem gcdIter_succ' : ∀ n u v, gcdIter (n + 1) u v = gcdStep (gcdIter n u v).1 (gcdIter n u v).2
  | 0, _, _ => rfl
  | n + 1, u, v => by rw [gcdIter, gcdIter_succ' n, gcdIter]

end VG.Proof.RsaKeyGen
