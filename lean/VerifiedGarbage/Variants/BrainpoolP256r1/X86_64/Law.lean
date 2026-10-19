module

public import VerifiedGarbage.Proof.BrainpoolP256r1.Curve
public import Mathlib.Data.BitVec
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvStep
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvMain
public import VerifiedGarbage.Proof.Weierstrass.InvArith
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvMain
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
public import VerifiedGarbage.Proof.BrainpoolP256r1.Point
public import VerifiedGarbage.Proof.Divstep.Incl
public import VerifiedGarbage.Proof.Divstep.Iter
public import VerifiedGarbage.Proof.Divstep.Packed
public import VerifiedGarbage.Proof.Divstep.Tc
public import VerifiedGarbage.Proof.Divstep.Word
public import VerifiedGarbage.Proof.Divstep.WordBasic
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.Bswap
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Mont.X86_64.Blocks
public import VerifiedGarbage.Proof.Mont.X86_64.CsubR
public import VerifiedGarbage.Proof.Mont.X86_64.CsubS
public import VerifiedGarbage.Proof.Mont.X86_64.Friendly
public import VerifiedGarbage.Proof.Mont.X86_64.Ops
public import VerifiedGarbage.Proof.Mont.X86_64.Round
public import VerifiedGarbage.Proof.Mont.X86_64.Sparse
public import VerifiedGarbage.Proof.Mont.X86_64.SparseX
public import VerifiedGarbage.Proof.Mont.X86_64.Wide
public import VerifiedGarbage.Proof.Mont.X86_64.WideOps
public import VerifiedGarbage.Proof.Weierstrass.Cubic
public import VerifiedGarbage.Proof.Weierstrass.Pow
public import VerifiedGarbage.Proof.Weierstrass.Words
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Bits
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvPacked
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvRed
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvWords
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontCall
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnB
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnN
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Words
public import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.BrainpoolP256r1.Point
import VerifiedGarbage.Proof.Divstep.Incl
import VerifiedGarbage.Proof.Divstep.Iter
import VerifiedGarbage.Proof.Divstep.Packed
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Divstep.Word
import VerifiedGarbage.Proof.Divstep.WordBasic
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Mont.X86_64.Blocks
import VerifiedGarbage.Proof.Mont.X86_64.CsubR
import VerifiedGarbage.Proof.Mont.X86_64.CsubS
import VerifiedGarbage.Proof.Mont.X86_64.Friendly
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Mont.X86_64.Round
import VerifiedGarbage.Proof.Mont.X86_64.Sparse
import VerifiedGarbage.Proof.Mont.X86_64.SparseX
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Mont.X86_64.WideOps
import VerifiedGarbage.Proof.Weierstrass.Cubic
import VerifiedGarbage.Proof.Weierstrass.Pow
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.X86_64.Bits
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvPacked
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvRed
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvWords
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontCall
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnB
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnN
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Weierstrass.X86_64.Words

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
