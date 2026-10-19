module

import VerifiedGarbage.Proof.Weierstrass.X86.InvMain
import VerifiedGarbage.Proof.Weierstrass.InvArith
public import VerifiedGarbage.Proof.Weierstrass.X86.InvInterface
public import VerifiedGarbage.Proof.BrainpoolP256r1.Curve
public import Mathlib.Data.BitVec
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# brainpoolP256r1's group law, on x86 (32-bit)

The variant of `BrainpoolP256r1` on x86 (32-bit) (see `TCB/Emit.lean`): not an implementation
but the facts the proofs of brainpoolP256r1's functions take, `Proof.BrainpoolP256r1.law` and
the soundness of the inversions by divsteps modulo a prime, whose proofs need Mathlib's algebra. Their registration files are generic over it
(`Generic/BrainpoolP256r1/X86/`, and `Generic/<Iface>/BrainpoolP256r1/X86/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

@[expose] public section

namespace VG.Variants.BrainpoolP256r1.X86.Law

def variant : Proof.Weierstrass.X86.Inv.HasLawInv Spec.BrainpoolP256r1.curve :=
  { law := Proof.BrainpoolP256r1.law
    inv := fun hp => Proof.Weierstrass.X86.Inv.invSound_of_toM hp (Proof.Weierstrass.invToM_of_prime hp) }

end VG.Variants.BrainpoolP256r1.X86.Law
