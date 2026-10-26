module
public import VerifiedGarbage.Spec.Rsa

import VerifiedGarbage.Proof.RsaKeyGen.KeyMath
import VerifiedGarbage.Proof.Rsa.KeyMath
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Data.Nat.Init
import Mathlib.Tactic.Attr.Core

/-!
# An RSA key from its primes: `d` by an exact division

The inverse of the specification, `Rsa.inverse e L`, as the ARMv7 code
computes it: for an odd `e ≥ 3`, from `x = L⁻¹ mod e` (`x L ≡ 1`, `x < e`),
`d = (L t + 1) / e` with `t = e − x`, an exact division
(`inverse_odd_exact`); none unless `L ≥ 2` and `gcd(L, e) = 1`
(`inverse_odd_none'`); for an even `e`, none unless `L` is odd, at least 3
and `gcd(e, L) = 1` (`inverse_even_none'`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen

open VG.Proof.Rsa (inverse_eq inverse_none)

/-- An odd `e ≥ 3` and `x = L⁻¹ mod e`: `e` divides `L (e − x) + 1`, whose
quotient is the inverse. -/
theorem inverse_odd_exact {e L x : Nat} (he3 : 3 ≤ e) (hL : 2 ≤ L) (hx : (e : Int) ∣ (x : Int) * L - 1)
    (hxe : x < e) : e ∣ L * (e - x) + 1 ∧ Spec.Rsa.inverse e L = some ((L * (e - x) + 1) / e) := by
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h
      obtain ⟨c, hc⟩ := hx
      simp at hc
      have := Int.eq_one_of_mul_eq_one_right (by omega)
        (show (e : Int) * (-c) = 1 by rw [Int.mul_neg, ← hc, Int.neg_neg])
      omega
    · exact h
  generalize ht : e - x = t
  have hte : t < e := by omega
  have hdv : e ∣ L * t + 1 := by
    have : ((L * t + 1 : Nat) : Int) = (e : Int) * L - ((x : Int) * L - 1) := by
      rw [← ht]; push_cast [Int.ofNat_sub (show x ≤ e by omega)]; grind
    have h' : (e : Int) ∣ ((L * t + 1 : Nat) : Int) := by
      rw [this]; exact Int.dvd_sub (Int.dvd_mul_right _ _) hx
    exact Int.natCast_dvd_natCast.mp h'
  refine ⟨hdv, ?_⟩
  obtain ⟨y, hy⟩ := hdv
  rw [hy, Nat.mul_div_cancel_left _ (by omega)]
  refine inverse_eq (by omega) ?_ ⟨t, ?_⟩
  · have : L * t + 1 < L * e := by
      have : L * t + L ≤ L * e := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hte
      omega
    have : e * y < e * L := by rw [← hy, Nat.mul_comm e L]; exact this
    exact Nat.lt_of_mul_lt_mul_left this
  · have : ((e * y : Nat) : Int) = ((L * t + 1 : Nat) : Int) := by rw [hy]
    push_cast at this ⊢
    grind

/-- An odd `e ≥ 3`: no inverse unless `L ≥ 2` and `gcd(L, e) = 1`. -/
theorem inverse_odd_none' {e L : Nat} (he3 : 3 ≤ e) (h : ¬ (2 ≤ L ∧ Nat.gcd L e = 1)) :
    Spec.Rsa.inverse e L = none := by
  rcases Nat.lt_or_ge L 2 with hl | hl
  · rcases (show L = 0 ∨ L = 1 by omega) with rfl | rfl
    · rw [inverse_mod_zero, ite_eq_right (show e ≠ 1 by omega)]
    · exact inverse_mod_one e
  · exact inverse_none fun h1 => h ⟨hl, by rw [Nat.gcd_comm]; exact h1⟩

/-- An even `e`: no inverse unless `L` is odd, at least 3, and `gcd(e, L) = 1`. -/
theorem inverse_even_none' {e L : Nat} (he : e % 2 = 0) (h : ¬ (L % 2 = 1 ∧ 3 ≤ L ∧ Nat.gcd e L = 1)) :
    Spec.Rsa.inverse e L = none := by
  refine inverse_even_none he fun ⟨h1, h2, h3⟩ => h ⟨h1, h2, ?_⟩
  rw [Nat.gcd_comm, Nat.gcd_rec]; exact h3

end VG.Proof.RsaKeyGen
