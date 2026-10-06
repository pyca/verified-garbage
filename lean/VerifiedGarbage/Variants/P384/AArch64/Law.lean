import VerifiedGarbage.Proof.P384.Curve
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvMain
import VerifiedGarbage.Proof.Weierstrass.InvArith

/-!
# P-384's group law, on AArch64

The variant of `P384` on AArch64 (see `TCB/Emit.lean`): not an implementation
but the facts the proofs of P-384's functions take, `Proof.P384.law` and the
soundness of the inversions by divsteps modulo a prime (`InvSounds`), whose
proofs need Mathlib's algebra.
Their registration files are generic over them
(`Generic/P384/AArch64/`, and `Generic/<Iface>/P384/AArch64/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

namespace VG.Variants.P384.AArch64.Law

open Proof.Weierstrass Proof.Weierstrass.AArch64

def variant : HasLawInv Spec.P384.curve :=
  ⟨Proof.P384.law, fun hp => invSound_of_toM hp (invToM_of_prime hp)⟩

end VG.Variants.P384.AArch64.Law
