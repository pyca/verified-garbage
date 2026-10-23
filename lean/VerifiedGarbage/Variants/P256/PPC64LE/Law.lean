module

public import VerifiedGarbage.Proof.P256.Curve
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Proof.P256.Point
public import VerifiedGarbage.Proof.P256.Prime
public import VerifiedGarbage.Proof.Weierstrass.Cubic
public import VerifiedGarbage.Proof.Weierstrass.Group
public import VerifiedGarbage.Proof.Weierstrass.RcbIdent
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.P256.Point
import VerifiedGarbage.Proof.P256.Prime
import VerifiedGarbage.Proof.Weierstrass.Cubic
import VerifiedGarbage.Proof.Weierstrass.Group
import VerifiedGarbage.Proof.Weierstrass.RcbIdent

/-!
# P-256's group law, on PPC64LE

The variant of `P256` on PPC64LE (see `TCB/Emit.lean`): not an implementation
but the fact the proofs of P-256's functions take, `Proof.P256.law`, whose
proof needs Mathlib's algebra. Their registration files are generic over it
(`Generic/P256/PPC64LE/`, and `Generic/<Iface>/P256/PPC64LE/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

@[expose] public section

namespace VG.Variants.P256.PPC64LE.Law

def variant : Proof.Weierstrass.HasLaw Spec.P256.curve := ⟨Proof.P256.law⟩

end VG.Variants.P256.PPC64LE.Law
