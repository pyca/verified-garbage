module

public import VerifiedGarbage.Proof.P521.Curve
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.P521.Point
public import VerifiedGarbage.Proof.Weierstrass.Cubic
import VerifiedGarbage.Proof.P521.Point
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-! # P-521's group law, on PPC64LE -/

@[expose] public section

namespace VG.Variants.P521.PPC64LE.Law

def variant : Proof.Weierstrass.HasLaw Spec.P521.curve := ⟨Proof.P521.law⟩

end VG.Variants.P521.PPC64LE.Law
