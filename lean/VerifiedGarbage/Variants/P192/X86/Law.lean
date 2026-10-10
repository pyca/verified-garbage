import VerifiedGarbage.Proof.P192.Curve

/-!
# P-192's group law, on x86 (32-bit)

The variant of `P192` on x86 (32-bit) (see `TCB/Emit.lean`): not an implementation
but the fact the proofs of P-192's functions take, `Proof.P192.law`, whose
proof needs Mathlib's algebra. Their registration files are generic over it
(`Generic/P192/X86/`, and `Generic/<Iface>/P192/X86/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

namespace VG.Variants.P192.X86.Law

def variant : Proof.Weierstrass.HasLaw Spec.P192.curve := ⟨Proof.P192.law⟩

end VG.Variants.P192.X86.Law
