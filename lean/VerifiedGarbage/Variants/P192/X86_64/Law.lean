import VerifiedGarbage.Proof.P192.Curve
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvMain
import VerifiedGarbage.Proof.Weierstrass.InvArith

/-!
# p192's group law and inversions, on x86-64

The variant of `P192` on x86-64 (see `TCB/Emit.lean`): not an implementation
but the facts the proofs of p192's functions take, `Proof.P192.law` and the
soundness of the inversions by divsteps modulo a prime (`InvSounds`), whose
proofs need Mathlib's algebra. Their registration files are generic over it
(`Generic/P192/X86_64/`, and `Generic/<Iface>/P192/X86_64/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

namespace VG.Variants.P192.X86_64.Law

open Proof.Weierstrass Proof.Weierstrass.X86_64

def variant : HasLawInv Spec.P192.curve :=
  ⟨Proof.P192.law, fun hp => invSound_of_toM hp (invToM_of_prime hp)⟩

end VG.Variants.P192.X86_64.Law
