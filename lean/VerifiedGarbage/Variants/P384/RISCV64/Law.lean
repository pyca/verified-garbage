module

public import VerifiedGarbage.Proof.P384.Curve
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.P384.Point
public import VerifiedGarbage.Proof.Weierstrass.Cubic
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-! # P-384's group law, on RISCV64 -/

@[expose] public section

namespace VG.Variants.P384.RISCV64.Law

def variant : Proof.Weierstrass.HasLaw Spec.P384.curve := ⟨Proof.P384.law⟩

end VG.Variants.P384.RISCV64.Law
