module

public import VerifiedGarbage.Proof.P521.Curve
public import VerifiedGarbage.Proof.P521.PrimeOrder
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvMain
public import VerifiedGarbage.Proof.Weierstrass.InvArith
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import VerifiedGarbage.Proof.Divstep.Bound
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-!
# P-521's group law, on AArch64

The variant of `P521` on AArch64 (see `TCB/Emit.lean`): not an implementation
but the facts the proofs of P-521's functions take, `Proof.P521.law` and the
soundness of the inversions by divsteps modulo a prime (`InvSounds`) and
its prime order (`Proof.P521.primeOrder`), whose proofs need Mathlib's algebra.
Their registration files are generic over them
(`Generic/P521/AArch64/`, and `Generic/<Iface>/P521/AArch64/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

@[expose] public section

namespace VG.Variants.P521.AArch64.Law

open Proof.Weierstrass Proof.Weierstrass.AArch64

def variant : HasLawInvOrd Spec.P521.curve :=
  ⟨⟨Proof.P521.law, fun hp => invSound_of_toM hp (invToM_of_prime hp)⟩, Proof.P521.primeOrder⟩

end VG.Variants.P521.AArch64.Law
