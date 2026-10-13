module

public import VerifiedGarbage.Proof.P256.Curve
public import VerifiedGarbage.Proof.P256.Order
public import VerifiedGarbage.Proof.Weierstrass.GroupOrder
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# P-256 has prime order

The base point has prime order `n` (`Order.lean`, `Prime.lean`), the curve
has no point of order 2 (`Curve.lean`), and `2p + 1 < 3n`, so the group of
points has `n` elements, and every point but `O` has order `n`
(`Weierstrass.primeOrder_of`). Only the variant files
`Variants/P256/<Target>/Law.lean` import this algebra.
-/

@[expose] public section

namespace VG.Proof.P256

open Spec.Weierstrass Weierstrass

theorem primeOrder : PrimeOrder Spec.P256.curve :=
  primeOrder_of good n_prime onCurve_G (mul_n law) (by decide +kernel)

end VG.Proof.P256
