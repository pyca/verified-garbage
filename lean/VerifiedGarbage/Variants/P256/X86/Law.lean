module

public import VerifiedGarbage.Proof.Weierstrass.X86.InvMain
public import VerifiedGarbage.Proof.Weierstrass.InvArith
public import VerifiedGarbage.Proof.P256.PrimeOrder
public import VerifiedGarbage.Proof.Weierstrass.X86.InvInterface
public import VerifiedGarbage.Proof.P256.Curve
import VerifiedGarbage.Proof.Divstep.Bound
import VerifiedGarbage.Proof.Weierstrass.X86.InvBatch
import VerifiedGarbage.Proof.X25519.X86.Column

/-!
# P-256's group law, on x86 (32-bit)

The variant of `P256` on x86 (32-bit) (see `TCB/Emit.lean`): not an implementation
but the fact the proofs of P-256's functions take, `Proof.P256.law`, whose
proof needs Mathlib's algebra. Their registration files are generic over it
(`Generic/P256/X86/`, and `Generic/<Iface>/P256/X86/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

@[expose] public section

namespace VG.Variants.P256.X86.Law

def variant : Proof.Weierstrass.X86.Inv.HasLawInvOrd Spec.P256.curve :=
  { law := Proof.P256.law
    inv := fun hp => Proof.Weierstrass.X86.Inv.invSound_of_toM hp (Proof.Weierstrass.invToM_of_prime hp)
    prime := Proof.P256.primeOrder }

end VG.Variants.P256.X86.Law
