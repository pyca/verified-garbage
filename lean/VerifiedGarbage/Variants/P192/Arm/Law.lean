module

public import VerifiedGarbage.Proof.P192.Curve
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.P192.Point
public import VerifiedGarbage.Proof.Weierstrass.Cubic
import VerifiedGarbage.Proof.P192.Point
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-! # P-192's group law, on 32-bit ARM -/

@[expose] public section

namespace VG.Variants.P192.Arm.Law

def variant : Proof.Weierstrass.HasLaw Spec.P192.curve := ⟨Proof.P192.law⟩

end VG.Variants.P192.Arm.Law
