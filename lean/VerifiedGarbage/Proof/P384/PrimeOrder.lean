import VerifiedGarbage.Proof.P384.Curve
import VerifiedGarbage.Proof.Weierstrass.Order
import VerifiedGarbage.Proof.Weierstrass.GroupOrder

/-!
# P-384 has prime order

The kernel evaluates the ladder for `n` from `G` (`ladRep_n`), whose `Z` is
zero, so `[n]G = O` (`mul_n`); `n` is prime (`Prime.lean`), the curve has no
point of order 2 (`Curve.lean`), and `2p + 1 < 3n`, so the group of points
has `n` elements, and every point but `O` has order `n`
(`Weierstrass.primeOrder_of`), which the window method in Jacobian
coordinates needs. Only the variant files `Variants/P384/<Target>/Law.lean`
import this algebra.
-/

namespace VG.Proof.P384

open Spec.Weierstrass Weierstrass

theorem ladRep_n : (ladRep Spec.P384.curve (Fin.ofNat _ Spec.P384.curve.gx)
    (Fin.ofNat _ Spec.P384.curve.gy) 1 Spec.P384.curve.n 384 384).2.2 = 0 := by
  decide +kernel

theorem mul_n : mul Spec.P384.curve.n (G Spec.P384.curve) = .infinity :=
  mul_n_of_ladRep law onCurve_G (by decide +kernel) ladRep_n

theorem primeOrder : PrimeOrder Spec.P384.curve := by
  haveI : Fact Spec.P384.curve.p.Prime := ⟨curve_p_prime⟩
  exact primeOrder_of good n_prime onCurve_G mul_n (by decide +kernel)

end VG.Proof.P384
