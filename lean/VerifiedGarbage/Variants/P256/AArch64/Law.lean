import VerifiedGarbage.Proof.P256.Curve

/-!
# P-256's group law, on AArch64

The variant of `P256` on AArch64 (see `TCB/Emit.lean`): not an implementation
but the fact the proofs of P-256's functions take, `Proof.P256.law`, whose
proof needs Mathlib's algebra. Their registration files are generic over it
(`Generic/P256/AArch64/`, and `Generic/<Iface>/P256/AArch64/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

namespace VG.Variants.P256.AArch64.Law

def variant : Proof.Weierstrass.HasLaw Spec.P256.curve := ⟨Proof.P256.law⟩

end VG.Variants.P256.AArch64.Law
