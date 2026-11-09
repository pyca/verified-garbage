module

public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.P192
import VerifiedGarbage.Proof.P192.Curve
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.P192.Point
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-! # P-192's group law, on x86 (32-bit) -/

public section

namespace VG.Proof.P192.X86

/-- P-192's group law, on x86 (32-bit), which the proofs of the curve's functions on this
target take. Not exposed: its importers need only its type, not the algebra
of its proof. -/
def hasLaw : Proof.Weierstrass.HasLaw Spec.P192.curve := ⟨Proof.P192.law⟩

end VG.Proof.P192.X86
