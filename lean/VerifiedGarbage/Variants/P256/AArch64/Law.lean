import VerifiedGarbage.Proof.P256.Curve
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvMain
import VerifiedGarbage.Proof.Weierstrass.InvArith

/-!
# P-256's group law, on AArch64

The variant of `P256` on AArch64 (see `TCB/Emit.lean`): not an implementation
but the facts the proofs of P-256's functions take, `Proof.P256.law` and the
inversions' soundness `Proof.Weierstrass.AArch64.invSounds`, whose proofs need
Mathlib's algebra and the divsteps' bound and arithmetic.
Their registration files are generic over them
(`Generic/P256/AArch64/`, and `Generic/<Iface>/P256/AArch64/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

namespace VG.Variants.P256.AArch64.Law

def variant : Proof.Weierstrass.AArch64.HasLaw Spec.P256.curve :=
  ⟨Proof.P256.law, Proof.Weierstrass.AArch64.invSounds Proof.Weierstrass.invToM⟩

end VG.Variants.P256.AArch64.Law
