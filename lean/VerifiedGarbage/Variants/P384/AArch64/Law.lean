import VerifiedGarbage.Proof.P384.Curve
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvMain
import VerifiedGarbage.Proof.Weierstrass.InvArith

/-!
# P-384's group law, on AArch64

The variant of `P384` on AArch64 (see `TCB/Emit.lean`): not an implementation
but the facts the proofs of P-384's functions take, `Proof.P384.law` and the
inversions' soundness `Proof.Weierstrass.AArch64.invSounds`, whose proofs need
Mathlib's algebra and the divsteps' bound and arithmetic.
Their registration files are generic over them
(`Generic/P384/AArch64/`, and `Generic/<Iface>/P384/AArch64/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

namespace VG.Variants.P384.AArch64.Law

def variant : Proof.Weierstrass.AArch64.HasLaw Spec.P384.curve :=
  ⟨Proof.P384.law, Proof.Weierstrass.AArch64.invSounds Proof.Weierstrass.invToM⟩

end VG.Variants.P384.AArch64.Law
