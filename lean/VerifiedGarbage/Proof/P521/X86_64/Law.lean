module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Spec.P521
import VerifiedGarbage.Proof.P521.Curve
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvMain
import VerifiedGarbage.Proof.Weierstrass.InvArith
import VerifiedGarbage.Proof.P521.PrimeOrder
import Mathlib.Data.BitVec
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvStep
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
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
import VerifiedGarbage.Proof.P521.Point
import VerifiedGarbage.Proof.Weierstrass.Cubic
import VerifiedGarbage.Proof.Weierstrass.GroupOrder
import VerifiedGarbage.Proof.Weierstrass.Pow
import VerifiedGarbage.Proof.Weierstrass.RcbIdent
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

/-! # P-521's group law and inversions, on x86-64 -/

public section

namespace VG.Proof.P521.X86_64

open Proof.Weierstrass Proof.Weierstrass.X86_64

/-- P-521's group law and inversions, on x86-64, which the proofs of the curve's functions on this
target take. Not exposed: its importers need only its type, not the algebra
of its proof. -/
def hasLaw : HasLawInvOrd Spec.P521.curve :=
  ⟨⟨Proof.P521.law, fun hp => invSound_of_toM hp (invToM_of_prime hp)⟩, Proof.P521.primeOrder,
    Proof.P521.killedByN⟩

end VG.Proof.P521.X86_64
