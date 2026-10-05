import VerifiedGarbage.Proof.P384.Curve
import VerifiedGarbage.Proof.Weierstrass.HasLaw
import VerifiedGarbage.Proof.Weierstrass.InvArith

/-!
# P-384's group law, on x86 (32-bit)

The variant of `P384` on x86 (32-bit) (see `TCB/Emit.lean`): not an implementation
but the facts the proofs of P-384's functions take, `Proof.P384.law` and the
inversions' `Proof.Weierstrass.invToM`, whose proofs need Mathlib's algebra.
Their registration files are generic over them
(`Generic/P384/X86/`, and `Generic/<Iface>/P384/X86/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

namespace VG.Variants.P384.X86.Law

def variant : Proof.Weierstrass.HasLaw Spec.P384.curve := ⟨Proof.P384.law, Proof.Weierstrass.invToM⟩

end VG.Variants.P384.X86.Law
