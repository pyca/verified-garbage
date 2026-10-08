import VerifiedGarbage.Proof.Secp256k1.Curve
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvMain
import VerifiedGarbage.Proof.Weierstrass.InvArith

/-!
# secp256k1's group law and inversions, on x86-64

The variant of `Secp256k1` on x86-64 (see `TCB/Emit.lean`): not an implementation
but the facts the proofs of secp256k1's functions take, `Proof.Secp256k1.law` and the
soundness of the inversions by divsteps modulo a prime (`InvSounds`), whose
proofs need Mathlib's algebra. Their registration files are generic over it
(`Generic/Secp256k1/X86_64/`, and `Generic/<Iface>/Secp256k1/X86_64/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

namespace VG.Variants.Secp256k1.X86_64.Law

open Proof.Weierstrass Proof.Weierstrass.X86_64

def variant : HasLawInv Spec.Secp256k1.curve :=
  ⟨Proof.Secp256k1.law, fun hp => invSound_of_toM hp (invToM_of_prime hp)⟩

end VG.Variants.Secp256k1.X86_64.Law
