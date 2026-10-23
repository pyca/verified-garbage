module

public import VerifiedGarbage.Proof.BrainpoolP256r1.Curve
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.BrainpoolP256r1.Point
public import VerifiedGarbage.Proof.Weierstrass.Cubic
import VerifiedGarbage.Proof.BrainpoolP256r1.Point
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-!
# brainpoolP256r1's group law, on PPC64LE

The variant of `BrainpoolP256r1` on PPC64LE (see `TCB/Emit.lean`): not an implementation
but the fact the proofs of brainpoolP256r1's functions take, `Proof.BrainpoolP256r1.law`, whose
proof needs Mathlib's algebra. Their registration files are generic over it
(`Generic/BrainpoolP256r1/PPC64LE/`, and `Generic/<Iface>/BrainpoolP256r1/PPC64LE/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

@[expose] public section

namespace VG.Variants.BrainpoolP256r1.PPC64LE.Law

def variant : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve := ⟨Proof.BrainpoolP256r1.law⟩

end VG.Variants.BrainpoolP256r1.PPC64LE.Law
