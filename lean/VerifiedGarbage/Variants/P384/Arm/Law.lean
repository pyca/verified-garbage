import VerifiedGarbage.Proof.P384.Curve

/-!
# P-384's group law, on 32-bit ARM

The variant of `P384` on 32-bit ARM (see `TCB/Emit.lean`): not an implementation
but the fact the proofs of P-384's functions take, `Proof.P384.law`, whose
proof needs Mathlib's algebra. Their registration files are generic over it
(`Generic/P384/Arm/`, and `Generic/<Iface>/P384/Arm/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

namespace VG.Variants.P384.Arm.Law

def variant : Proof.Weierstrass.HasLaw Spec.P384.curve := ⟨Proof.P384.law⟩

end VG.Variants.P384.Arm.Law
