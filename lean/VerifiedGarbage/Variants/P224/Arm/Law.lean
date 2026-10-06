import VerifiedGarbage.Proof.P224.Curve

/-!
# P-224's group law, on 32-bit ARM

The variant of `P224` on 32-bit ARM (see `TCB/Emit.lean`): not an implementation
but the fact the proofs of P-224's functions take, `Proof.P224.law`, whose
proof needs Mathlib's algebra. Their registration files are generic over it
(`Generic/P224/Arm/`, and `Generic/<Iface>/P224/Arm/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

namespace VG.Variants.P224.Arm.Law

def variant : Proof.Weierstrass.HasLaw Spec.P224.curve := ⟨Proof.P224.law⟩

end VG.Variants.P224.Arm.Law
