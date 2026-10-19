module

public import VerifiedGarbage.Proof.BrainpoolP256r1.Curve
public import Mathlib.Data.BitVec
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvStep
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvMain
import VerifiedGarbage.Proof.Weierstrass.InvArith
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# brainpoolP256r1's group law and inversions, on x86-64

The variant of `BrainpoolP256r1` on x86-64 (see `TCB/Emit.lean`): not an implementation
but the facts the proofs of brainpoolP256r1's functions take, `Proof.BrainpoolP256r1.law` and the
soundness of the inversions by divsteps modulo a prime (`InvSounds`), whose
proofs need Mathlib's algebra. Their registration files are generic over it
(`Generic/BrainpoolP256r1/X86_64/`, and `Generic/<Iface>/BrainpoolP256r1/X86_64/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

@[expose] public section

namespace VG.Variants.BrainpoolP256r1.X86_64.Law

open Proof.Weierstrass Proof.Weierstrass.X86_64

def variant : HasLawInv Spec.BrainpoolP256r1.curve :=
  ⟨Proof.BrainpoolP256r1.law, fun hp => invSound_of_toM hp (invToM_of_prime hp)⟩

end VG.Variants.BrainpoolP256r1.X86_64.Law
