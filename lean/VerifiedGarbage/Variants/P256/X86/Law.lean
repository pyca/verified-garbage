import VerifiedGarbage.Proof.P256.Curve
import VerifiedGarbage.Proof.Weierstrass.HasLaw
import VerifiedGarbage.Proof.Weierstrass.InvArith

/-!
# P-256's group law, on x86 (32-bit)

The variant of `P256` on x86 (32-bit) (see `TCB/Emit.lean`): not an implementation
but the facts the proofs of P-256's functions take, `Proof.P256.law` and the
inversions' `Proof.Weierstrass.invToM`, whose proofs need Mathlib's algebra.
Their registration files are generic over them
(`Generic/P256/X86/`, and `Generic/<Iface>/P256/X86/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

namespace VG.Variants.P256.X86.Law

def variant : Proof.Weierstrass.HasLaw Spec.P256.curve := ⟨Proof.P256.law, Proof.Weierstrass.invToM⟩

end VG.Variants.P256.X86.Law
