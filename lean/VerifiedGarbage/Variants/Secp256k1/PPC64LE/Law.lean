module

public import VerifiedGarbage.Proof.Secp256k1.Curve
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Secp256k1.Point
public import VerifiedGarbage.Proof.Weierstrass.Cubic
import VerifiedGarbage.Proof.Secp256k1.Point
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-! # secp256k1's group law, on PPC64LE -/

@[expose] public section

namespace VG.Variants.Secp256k1.PPC64LE.Law

def variant : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve := ⟨Proof.Secp256k1.law⟩

end VG.Variants.Secp256k1.PPC64LE.Law
