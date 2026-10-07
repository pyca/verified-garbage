import VerifiedGarbage.Proof.P256.Curve
import VerifiedGarbage.Proof.P256.PrimeOrder
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvMain
import VerifiedGarbage.Proof.Weierstrass.InvArith

/-!
# P-256's group law, inversions and prime order, on x86-64

The variant of `P256` on x86-64 (see `TCB/Emit.lean`): not an implementation
but the facts the proofs of P-256's functions take, `Proof.P256.law`, the
soundness of the inversions by divsteps modulo a prime (`InvSounds`) and that
the curve has prime order (`Proof.P256.primeOrder`), whose proofs need
Mathlib's algebra. Their registration files are generic over it
(`Generic/P256/X86_64/`, and `Generic/<Iface>/P256/X86_64/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

namespace VG.Variants.P256.X86_64.Law

open Proof.Weierstrass Proof.Weierstrass.X86_64

def variant : HasLawInvOrd Spec.P256.curve where
  law := Proof.P256.law
  inv := fun hp => invSound_of_toM hp (invToM_of_prime hp)
  prime := Proof.P256.primeOrder

end VG.Variants.P256.X86_64.Law
