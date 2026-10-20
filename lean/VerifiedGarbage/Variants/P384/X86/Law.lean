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

/-!
# P-384's group law, on x86 (32-bit)

The variant of `P384` on x86 (32-bit) (see `TCB/Emit.lean`): not an implementation
but the fact the proofs of P-384's functions take, `Proof.P384.law`, whose
proof needs Mathlib's algebra. Their registration files are generic over it
(`Generic/P384/X86/`, and `Generic/<Iface>/P384/X86/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

@[expose] public section

namespace VG.Variants.P384.X86.Law

def variant : Proof.Weierstrass.HasLaw Spec.P384.curve := ⟨Proof.P384.law⟩

end VG.Variants.P384.X86.Law
