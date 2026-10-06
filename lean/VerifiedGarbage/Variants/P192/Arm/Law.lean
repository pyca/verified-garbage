import VerifiedGarbage.Proof.P192.Curve

/-!
# P-192's group law, on 32-bit ARM

The variant of `P192` on 32-bit ARM (see `TCB/Emit.lean`): not an implementation
but the fact the proofs of P-192's functions take, `Proof.P192.law`, whose
proof needs Mathlib's algebra. Their registration files are generic over it
(`Generic/P192/Arm/`, and `Generic/<Iface>/P192/Arm/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

namespace VG.Variants.P192.Arm.Law

def variant : Proof.Weierstrass.HasLaw Spec.P192.curve := ⟨Proof.P192.law⟩

end VG.Variants.P192.Arm.Law
