module

public import VerifiedGarbage.Proof.P224.Curve
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.P224.Point
public import VerifiedGarbage.Proof.Weierstrass.Cubic
import VerifiedGarbage.Proof.P224.Point
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-! # P-224's group law, on PPC64LE -/

@[expose] public section

namespace VG.Variants.P224.PPC64LE.Law

def variant : Proof.Weierstrass.HasLaw Spec.P224.curve := ⟨Proof.P224.law⟩

end VG.Variants.P224.PPC64LE.Law
