import VerifiedGarbage.Proof.P521.Curve
import VerifiedGarbage.Proof.Weierstrass.HasLaw
import VerifiedGarbage.Proof.Weierstrass.InvArith

/-!
# P-521's group law, on x86-64

The variant of `P521` on x86-64 (see `TCB/Emit.lean`): not an implementation
but the facts the proofs of P-521's functions take, `Proof.P521.law` and the
inversions' `Proof.Weierstrass.invToM`, whose proofs need Mathlib's algebra.
Their registration files are generic over them
(`Generic/P521/X86_64/`, and `Generic/<Iface>/P521/X86_64/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

namespace VG.Variants.P521.X86_64.Law

def variant : Proof.Weierstrass.HasLaw Spec.P521.curve := ⟨Proof.P521.law, Proof.Weierstrass.invToM⟩

end VG.Variants.P521.X86_64.Law
