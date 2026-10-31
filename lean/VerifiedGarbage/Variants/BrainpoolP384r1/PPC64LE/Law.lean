module

public import VerifiedGarbage.Proof.BrainpoolP384r1.Curve
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.BrainpoolP384r1.Point
public import VerifiedGarbage.Proof.Weierstrass.Cubic
import VerifiedGarbage.Proof.BrainpoolP384r1.Point
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-! # brainpoolP384r1's group law, on PPC64LE -/

@[expose] public section

namespace VG.Variants.BrainpoolP384r1.PPC64LE.Law

def variant : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve := ⟨Proof.BrainpoolP384r1.law⟩

end VG.Variants.BrainpoolP384r1.PPC64LE.Law
