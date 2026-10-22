module

import VerifiedGarbage.Proof.P384.Curve
public import VerifiedGarbage.Proof.Weierstrass.Order
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Spec.P384
import VerifiedGarbage.Proof.Weierstrass.GroupOrder
import VerifiedGarbage.Proof.P384.Prime
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.P384.Order

/-!
# P-384 has prime order

`[n]G = O` (`mul_n`, from `Order.lean`); `n` is prime (`Prime.lean`), the curve has no
point of order 2 (`Curve.lean`), and `2p + 1 < 3n`, so the group of points
has `n` elements, and every point but `O` has order `n`
(`Weierstrass.primeOrder_of`), which the window method in Jacobian
coordinates needs. Only the variant files `Variants/P384/<Target>/Law.lean`
import this algebra.
public import Aesop.BuiltinRules
-/

@[expose] public section

namespace VG.Proof.P384

open Spec.Weierstrass Weierstrass

theorem mul_n : mul Spec.P384.curve.n (G Spec.P384.curve) = .infinity := mul_n_of law

theorem primeOrder : PrimeOrder Spec.P384.curve := by
  haveI : Fact Spec.P384.curve.p.Prime := ⟨curve_p_prime⟩
  exact primeOrder_of good n_prime onCurve_G mul_n (by decide +kernel)

/-- `n` kills every point: the group has `n` elements. -/
theorem killedByN : KilledByN Spec.P384.curve := by
  haveI : Fact Spec.P384.curve.p.Prime := ⟨curve_p_prime⟩
  exact killedByN_of good n_prime onCurve_G mul_n (by decide +kernel)

end VG.Proof.P384
