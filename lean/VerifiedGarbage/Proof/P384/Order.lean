module

import VerifiedGarbage.Proof.P384.Prime
import VerifiedGarbage.Proof.P384.Point
public import VerifiedGarbage.Proof.Weierstrass.Order
public import VerifiedGarbage.Proof.Weierstrass.Booth
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.P384
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Finiteness.Attr
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual

/-!
# P-384: `G` has order `n`, for the comb with Booth's digits

The kernel evaluates the ladder for `n` (`ladRep_n`), whose `Z` is zero, so
`[n]G = O` (`mul_n`); `n` is prime (`Prime.lean`), so the multiples of `G`
below `n` are coprime to it (`n_cop`).
-/

@[expose] public section

namespace VG.Proof.P384

open Spec.Weierstrass Weierstrass

theorem ladRep_n : (ladRep Spec.P384.curve (Fin.ofNat _ Spec.P384.curve.gx)
    (Fin.ofNat _ Spec.P384.curve.gy) 1 Spec.P384.curve.n 384 384).2.2 = 0 := by
  decide +kernel

theorem mul_n_of (hC : Law Spec.P384.curve) : mul Spec.P384.curve.n (G Spec.P384.curve) = .infinity :=
  mul_n_of_ladRep hC onCurve_G (by decide +kernel) ladRep_n

theorem n_cop : ∀ m, 0 < m → m < Spec.P384.curve.n → Nat.gcd m Spec.P384.curve.n = 1 := by
  intro m h0 h1
  rcases n_prime.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_right m Spec.P384.n) with h | h
  · exact h
  · have : Spec.P384.n ∣ m := h ▸ Nat.gcd_dvd_left m Spec.P384.n
    exact absurd (Nat.le_of_dvd h0 this) (by show ¬ (Spec.P384.n ≤ m); exact Nat.not_le.mpr h1)

/-- What the comb with Booth's digits needs of P-384, for its `55` digits of
`7` bits and scalars below `2³⁸⁴` (`2 ^ (64 k)` for its `k = 6` words, as
callers state it, so that no one evaluates the power). -/
theorem booth (hC : Law Spec.P384.curve) {J k : Nat} (hJ : J = 55) (hk : k = 6) :
    BoothOk Spec.P384.curve 7 J (2 ^ (64 * k)) := by
  subst hJ hk
  exact ⟨mul_n_of hC, by decide, n_cop, by decide +kernel, by decide, by decide +kernel⟩

end VG.Proof.P384
