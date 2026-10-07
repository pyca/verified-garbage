import VerifiedGarbage.Proof.P521.Curve
import VerifiedGarbage.Proof.Weierstrass.Card
import VerifiedGarbage.Proof.Weierstrass.Order
import VerifiedGarbage.Proof.Weierstrass.WindowJ

/-!
# P-521: every point has order `n`

The kernel evaluates the ladder for `n` from `G` (`ladRep_n`), whose `Z` is
zero, so `[n]G = O` (`mul_n`); `n` is prime (`Prime.lean`) and `2p + 1 < 3n`,
so the curve has `n` points and `[n]P = O` for every point `P` of it
(`Good.mul_n`, `Proof/Weierstrass/Card.lean`): `ordN`, which the window
method in Jacobian coordinates needs. It needs Mathlib's group theory, so only
the variant files `Variants/P521/<Target>/Law.lean` import it.
-/

namespace VG.Proof.P521

open Spec.Weierstrass Weierstrass

theorem ladRep_n : (ladRep Spec.P521.curve (Fin.ofNat _ Spec.P521.curve.gx)
    (Fin.ofNat _ Spec.P521.curve.gy) 1 Spec.P521.curve.n 521 521).2.2 = 0 := by
  decide +kernel

theorem mul_n : mul Spec.P521.curve.n (G Spec.P521.curve) = .infinity :=
  mul_n_of_ladRep law onCurve_G (by decide +kernel) ladRep_n

theorem n_cop : ∀ m, 0 < m → m < Spec.P521.curve.n → Nat.gcd m Spec.P521.curve.n = 1 := by
  intro m h0 h1
  rcases n_prime.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_right m Spec.P521.n) with h | h
  · exact h
  · have : Spec.P521.n ∣ m := h ▸ Nat.gcd_dvd_left m Spec.P521.n
    exact absurd (Nat.le_of_dvd h0 this) (by show ¬ (Spec.P521.n ≤ m); exact Nat.not_le.mpr h1)

/-- Every point of P-521 has order dividing `n`, a prime. -/
theorem ordN : OrdN Spec.P521.curve where
  pos := by decide +kernel
  cop := n_cop
  mul_n := fun hP => by
    haveI : Fact Spec.P521.curve.p.Prime := ⟨curve_p_prime⟩
    exact good.mul_n n_prime onCurve_G (fun h => nomatch h) mul_n (by decide +kernel) hP

end VG.Proof.P521
