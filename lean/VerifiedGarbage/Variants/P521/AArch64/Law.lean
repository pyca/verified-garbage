import VerifiedGarbage.Proof.P521.Curve
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvMain
import VerifiedGarbage.Proof.Weierstrass.InvArith

/-!
# P-521's group law, on AArch64

The variant of `P521` on AArch64 (see `TCB/Emit.lean`): not an implementation
but the facts the proofs of P-521's functions take, `Proof.P521.law` and the
inversions' soundness `Proof.Weierstrass.AArch64.invSounds`, whose proofs need
Mathlib's algebra and the divsteps' bound and arithmetic.
Their registration files are generic over them
(`Generic/P521/AArch64/`, and `Generic/<Iface>/P521/AArch64/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

namespace VG.Variants.P521.AArch64.Law

def variant : Proof.Weierstrass.AArch64.HasLaw Spec.P521.curve :=
  ⟨Proof.P521.law, Proof.Weierstrass.AArch64.invSounds Proof.Weierstrass.invToM⟩

end VG.Variants.P521.AArch64.Law
