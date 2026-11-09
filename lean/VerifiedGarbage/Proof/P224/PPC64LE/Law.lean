module

public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.P224
import VerifiedGarbage.Proof.P224.Curve
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.P224.Point
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-! # P-224's group law, on PPC64LE -/

public section

namespace VG.Proof.P224.PPC64LE

/-- P-224's group law, on PPC64LE, which the proofs of the curve's functions on this
target take. Not exposed: its importers need only its type, not the algebra
of its proof. -/
def hasLaw : Proof.Weierstrass.HasLaw Spec.P224.curve := ⟨Proof.P224.law⟩

end VG.Proof.P224.PPC64LE
