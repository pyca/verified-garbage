module

public import VerifiedGarbage.Proof.P256.Curve
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset

/-!
# P-256's group law, on 32-bit ARM

The variant of `P256` on 32-bit ARM (see `TCB/Emit.lean`): not an implementation
but the fact the proofs of P-256's functions take, `Proof.P256.law`, whose
proof needs Mathlib's algebra. Their registration files are generic over it
(`Generic/P256/Arm/`, and `Generic/<Iface>/P256/Arm/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

@[expose] public section

namespace VG.Variants.P256.Arm.Law

def variant : Proof.Weierstrass.HasLaw Spec.P256.curve := ⟨Proof.P256.law⟩

end VG.Variants.P256.Arm.Law
