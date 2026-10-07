import VerifiedGarbage.Spec.Weierstrass

/-!
# Curves of prime order

`PrimeOrder C`: every point of the curve `C` but the point at infinity has
order `n` (`C.n`), so the group of its points is cyclic of prime order `n`
(the cofactor is 1) and any of them generates it. A statement only, without
the algebra of its proofs (e.g. `Proof/P256/PrimeOrder.lean`, from
`Proof/Weierstrass/GroupOrder.lean`), so that the proofs of the code can take
it as a hypothesis.
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

/-- Every point of `C` but the point at infinity has order `C.n`. -/
def PrimeOrder (C : Curve) : Prop :=
  ∀ P : Point C, onCurve C P = true → P ≠ .infinity → ∀ m : Nat, mul m P = .infinity → C.n ∣ m

end VG.Proof.Weierstrass
