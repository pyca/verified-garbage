module

public import VerifiedGarbage.Proof.BrainpoolP384r1.Curve
public import Mathlib.Data.BitVec
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvMain
import VerifiedGarbage.Proof.Weierstrass.InvArith
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# brainpoolP384r1's group law and inversions, on AArch64

The variant of `BrainpoolP384r1` on AArch64 (see `TCB/Emit.lean`): not an implementation
but the facts the proofs of brainpoolP384r1's functions take, `Proof.BrainpoolP384r1.law` and the
soundness of the inversions by divsteps modulo a prime (`InvSounds`), whose
proofs need Mathlib's algebra. Their registration files are generic over it
(`Generic/BrainpoolP384r1/AArch64/`, and `Generic/<Iface>/BrainpoolP384r1/AArch64/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

@[expose] public section

namespace VG.Variants.BrainpoolP384r1.AArch64.Law

open Proof.Weierstrass Proof.Weierstrass.AArch64

def variant : HasLawInv Spec.BrainpoolP384r1.curve :=
  ⟨Proof.BrainpoolP384r1.law, fun hp => invSound_of_toM hp (invToM_of_prime hp)⟩

end VG.Variants.BrainpoolP384r1.AArch64.Law
