import VerifiedGarbage.Proof.P521.Curve
import VerifiedGarbage.Proof.Weierstrass.Order
import VerifiedGarbage.Proof.Weierstrass.GroupOrder

/-!
# P-521 has prime order

The kernel evaluates the ladder for `n` from `G` (`ladRep_n`), whose `Z` is
zero, so `[n]G = O` (`mul_n`); `n` is prime (`Prime.lean`), the curve has no
point of order 2 (`Curve.lean`), and `2p + 1 < 3n`, so the group of points
has `n` elements, and every point but `O` has order `n`
(`Weierstrass.primeOrder_of`), which the window method in Jacobian
coordinates needs. Only the variant files `Variants/P521/<Target>/Law.lean`
import this algebra.
-/

namespace VG.Proof.P521

open Spec.Weierstrass Weierstrass

theorem ladRep_n : (ladRep Spec.P521.curve (Fin.ofNat _ Spec.P521.curve.gx)
    (Fin.ofNat _ Spec.P521.curve.gy) 1 Spec.P521.curve.n 521 521).2.2 = 0 := by
  decide +kernel

theorem mul_n : mul Spec.P521.curve.n (G Spec.P521.curve) = .infinity :=
  mul_n_of_ladRep law onCurve_G (by decide +kernel) ladRep_n

theorem primeOrder : PrimeOrder Spec.P521.curve := by
  haveI : Fact Spec.P521.curve.p.Prime := ⟨curve_p_prime⟩
  exact primeOrder_of good n_prime onCurve_G mul_n (by decide +kernel)

end VG.Proof.P521
