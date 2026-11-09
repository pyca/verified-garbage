module

public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.P256
import VerifiedGarbage.Proof.P256.Curve
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.P256.Point
import VerifiedGarbage.Proof.P256.Prime
import VerifiedGarbage.Proof.Weierstrass.Cubic
import VerifiedGarbage.Proof.Weierstrass.Group
import VerifiedGarbage.Proof.Weierstrass.RcbIdent

/-! # P-256's group law, on 32-bit ARM -/

public section

namespace VG.Proof.P256.Arm

/-- P-256's group law, on 32-bit ARM, which the proofs of the curve's functions on this
target take. Not exposed: its importers need only its type, not the algebra
of its proof. -/
def hasLaw : Proof.Weierstrass.HasLaw Spec.P256.curve := ⟨Proof.P256.law⟩

end VG.Proof.P256.Arm
