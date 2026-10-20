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

/-!
# secp256k1's group law, on 32-bit ARM

The variant of `Secp256k1` on 32-bit ARM (see `TCB/Emit.lean`): not an implementation
but the fact the proofs of secp256k1's functions take, `Proof.Secp256k1.law`, whose
proof needs Mathlib's algebra. Their registration files are generic over it
(`Generic/Secp256k1/Arm/`, and `Generic/<Iface>/Secp256k1/Arm/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

@[expose] public section

namespace VG.Variants.Secp256k1.Arm.Law

def variant : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve := ⟨Proof.Secp256k1.law⟩

end VG.Variants.Secp256k1.Arm.Law
