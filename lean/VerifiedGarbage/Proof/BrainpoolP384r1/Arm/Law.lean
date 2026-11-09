module

public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.BrainpoolP384r1
import VerifiedGarbage.Proof.BrainpoolP384r1.Curve
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.BrainpoolP384r1.Point
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-! # brainpoolP384r1's group law, on 32-bit ARM -/

public section

namespace VG.Proof.BrainpoolP384r1.Arm

/-- brainpoolP384r1's group law, on 32-bit ARM, which the proofs of the curve's functions on this
target take. Not exposed: its importers need only its type, not the algebra
of its proof. -/
def hasLaw : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve := ⟨Proof.BrainpoolP384r1.law⟩

end VG.Proof.BrainpoolP384r1.Arm
