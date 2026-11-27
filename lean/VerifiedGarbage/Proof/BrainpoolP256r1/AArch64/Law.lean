module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Spec.BrainpoolP256r1
import VerifiedGarbage.Proof.BrainpoolP256r1.Curve
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvMain
import VerifiedGarbage.Proof.Weierstrass.InvArith
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import VerifiedGarbage.Proof.Divstep.Bound
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.BrainpoolP256r1.Point
import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Divstep.Word
import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.AArch64.Comb
import VerifiedGarbage.Proof.Weierstrass.AArch64.CombSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvRed
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvWords
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Weierstrass.Cubic
import VerifiedGarbage.Proof.Weierstrass.Law3
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Divstep.Incl

/-! # brainpoolP256r1's group law and inversions, on AArch64 -/

public section

namespace VG.Proof.BrainpoolP256r1.AArch64

open Proof.Weierstrass Proof.Weierstrass.AArch64

/-- brainpoolP256r1's group law and inversions, on AArch64, which the proofs of the curve's functions on this
target take. Not exposed: its importers need only its type, not the algebra
of its proof. -/
def hasLaw : HasLawInv Spec.BrainpoolP256r1.curve :=
  ⟨Proof.BrainpoolP256r1.law, fun hp => invSound_of_toM hp (invToM_of_prime hp)⟩

end VG.Proof.BrainpoolP256r1.AArch64
