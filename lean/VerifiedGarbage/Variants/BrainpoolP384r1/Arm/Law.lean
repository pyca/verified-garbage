module

public import VerifiedGarbage.Proof.BrainpoolP384r1.Curve
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# brainpoolP384r1's group law, on 32-bit ARM

The variant of `BrainpoolP384r1` on 32-bit ARM (see `TCB/Emit.lean`): not an implementation
but the fact the proofs of brainpoolP384r1's functions take, `Proof.BrainpoolP384r1.law`, whose
proof needs Mathlib's algebra. Their registration files are generic over it
(`Generic/BrainpoolP384r1/Arm/`, and `Generic/<Iface>/BrainpoolP384r1/Arm/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

@[expose] public section

namespace VG.Variants.BrainpoolP384r1.Arm.Law

def variant : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve := ⟨Proof.BrainpoolP384r1.law⟩

end VG.Variants.BrainpoolP384r1.Arm.Law
