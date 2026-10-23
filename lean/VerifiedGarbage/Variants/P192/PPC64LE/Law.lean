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

/-!
# P-192's group law, on PPC64LE

The variant of `P192` on PPC64LE (see `TCB/Emit.lean`): not an implementation
but the fact the proofs of P-192's functions take, `Proof.P192.law`, whose
proof needs Mathlib's algebra. Their registration files are generic over it
(`Generic/P192/PPC64LE/`, and `Generic/<Iface>/P192/PPC64LE/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

@[expose] public section

namespace VG.Variants.P192.PPC64LE.Law

def variant : Proof.Weierstrass.HasLaw Spec.P192.curve := ⟨Proof.P192.law⟩

end VG.Variants.P192.PPC64LE.Law
