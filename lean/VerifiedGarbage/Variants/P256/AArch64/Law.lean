import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
import VerifiedGarbage.Proof.P256.Curve
import VerifiedGarbage.Proof.P256.PrimeOrder
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvMain
import VerifiedGarbage.Proof.Weierstrass.InvArith

/-!
# P-256's group law, on AArch64

The variant of `P256` on AArch64 (see `TCB/Emit.lean`): not an implementation
but the facts the proofs of P-256's functions take, `Proof.P256.law` and the
soundness of the inversions by divsteps modulo a prime (`InvSounds`), whose
proofs need Mathlib's algebra.
Their registration files are generic over them
(`Generic/P256/AArch64/`, and `Generic/<Iface>/P256/AArch64/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

namespace VG.Variants.P256.AArch64.Law

open Proof.Weierstrass Proof.Weierstrass.AArch64

def variant : HasLawInvToMOrd Spec.P256.curve :=
  ⟨⟨⟨Proof.P256.law, fun hp => invSound_of_toM hp (invToM_of_prime hp)⟩,
    invToM_of_prime Proof.P256.n_prime⟩, Proof.P256.primeOrder, invToM_of_prime Proof.P256.p_prime⟩

end VG.Variants.P256.AArch64.Law
