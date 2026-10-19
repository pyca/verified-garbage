module

import VerifiedGarbage.Proof.Weierstrass.X86.InvMain
import VerifiedGarbage.Proof.Weierstrass.InvArith
public import VerifiedGarbage.Proof.Weierstrass.X86.InvInterface
public import VerifiedGarbage.Proof.Secp256k1.Curve
public import Mathlib.Data.BitVec
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# secp256k1's group law, on x86 (32-bit)

The variant of `Secp256k1` on x86 (32-bit) (see `TCB/Emit.lean`): not an implementation
but the facts the proofs of secp256k1's functions take, `Proof.Secp256k1.law` and
the soundness of the inversions by divsteps modulo a prime, whose proofs need Mathlib's algebra. Their registration files are generic over it
(`Generic/Secp256k1/X86/`, and `Generic/<Iface>/Secp256k1/X86/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

@[expose] public section

namespace VG.Variants.Secp256k1.X86.Law

def variant : Proof.Weierstrass.X86.Inv.HasLawInv Spec.Secp256k1.curve :=
  { law := Proof.Secp256k1.law
    inv := fun hp => Proof.Weierstrass.X86.Inv.invSound_of_toM hp (Proof.Weierstrass.invToM_of_prime hp) }

end VG.Variants.Secp256k1.X86.Law
