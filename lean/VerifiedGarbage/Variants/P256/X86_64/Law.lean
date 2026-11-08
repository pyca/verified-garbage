module

public import VerifiedGarbage.Proof.P256.Curve
public import VerifiedGarbage.Proof.P256.PrimeOrder
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import Mathlib.Data.BitVec
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvStep
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvMain
public import VerifiedGarbage.Proof.Weierstrass.InvArith
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
public import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.Weierstrass.Booth
public import VerifiedGarbage.Proof.Divstep.Incl
public import VerifiedGarbage.Proof.Divstep.Iter
public import VerifiedGarbage.Proof.Divstep.Packed
public import VerifiedGarbage.Proof.Divstep.Tc
public import VerifiedGarbage.Proof.Divstep.Word
public import VerifiedGarbage.Proof.Divstep.WordBasic
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Pratt
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
public import VerifiedGarbage.Proof.P256.Point
public import VerifiedGarbage.Proof.P256.Prime
public import VerifiedGarbage.Proof.Weierstrass.Cubic
public import VerifiedGarbage.Proof.Weierstrass.GroupOrder
public import VerifiedGarbage.Proof.Weierstrass.Pow
public import VerifiedGarbage.Proof.Weierstrass.RcbIdent
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

/-! # P-256's group law, inversions and prime order, on x86-64 -/

@[expose] public section

namespace VG.Variants.P256.X86_64.Law

open Proof.Weierstrass Proof.Weierstrass.X86_64

def variant : HasLawInvOrd Spec.P256.curve where
  law := Proof.P256.law
  inv := fun hp => invSound_of_toM hp (invToM_of_prime hp)
  prime := Proof.P256.primeOrder
  killed := Proof.P256.killedByN

end VG.Variants.P256.X86_64.Law
