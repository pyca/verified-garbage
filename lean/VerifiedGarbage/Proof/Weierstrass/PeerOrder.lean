import VerifiedGarbage.Proof.Weierstrass.Booth

/-! Group-order facts for scalar multiplication of arbitrary validated peers. -/
namespace VG.Proof.Weierstrass
open Spec.Weierstrass

/-- Every point is killed by n, and a nonzero point's scalar collisions are
congruent modulo n. The interface keeps Mathlib out of implementation proofs. -/
structure PeerOrder (C : Curve) : Prop where
  mul_n : ∀ {P : Point C}, onCurve C P = true → mul C.n P = .infinity
  zmul_dvd : ∀ {P : Point C}, onCurve C P = true → P ≠ .infinity →
    ∀ {a b : Int}, zmul a P = zmul b P → (C.n : Int) ∣ a - b

/-- A proof interface value for artifact specialization. -/
structure HasPeerOrder (C : Curve) : Type where
  order : PeerOrder C

end VG.Proof.Weierstrass
