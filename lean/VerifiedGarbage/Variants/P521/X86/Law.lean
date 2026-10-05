import VerifiedGarbage.Proof.P521.Curve

/-!
# P-521's group law, on x86 (32-bit)

The variant of `P521` on x86 (32-bit) (see `TCB/Emit.lean`): not an implementation
but the fact the proofs of P-521's functions take, `Proof.P521.law`, whose
proof needs Mathlib's algebra. Their registration files are generic over it
(`Generic/P521/X86/`, and `Generic/<Iface>/P521/X86/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

namespace VG.Variants.P521.X86.Law

def variant : Proof.Weierstrass.HasLaw Spec.P521.curve := ⟨Proof.P521.law⟩

end VG.Variants.P521.X86.Law
