import VerifiedGarbage.Proof.P384.Curve

/-!
# P-384's group law, on x86-64

The variant of `P384` on x86-64 (see `TCB/Emit.lean`): not an implementation
but the fact the proofs of P-384's functions take, `Proof.P384.law`, whose
proof needs Mathlib's algebra. Their registration files are generic over it
(`Generic/P384/X86_64/`, and `Generic/<Iface>/P384/X86_64/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

namespace VG.Variants.P384.X86_64.Law

def variant : Proof.Weierstrass.HasLaw Spec.P384.curve := ⟨Proof.P384.law⟩

end VG.Variants.P384.X86_64.Law
