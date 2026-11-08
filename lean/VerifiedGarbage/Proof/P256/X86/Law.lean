module

public import VerifiedGarbage.Proof.Weierstrass.X86.InvInterface
public import VerifiedGarbage.Spec.P256
import VerifiedGarbage.Proof.Weierstrass.X86.InvMain
import VerifiedGarbage.Proof.Weierstrass.InvArith
import VerifiedGarbage.Proof.P256.PrimeOrder
import VerifiedGarbage.Proof.P256.Curve
import Mathlib.Data.BitVec
import VerifiedGarbage.Proof.Divstep.Bound
import VerifiedGarbage.Proof.Weierstrass.X86.InvBatch
import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.Weierstrass.Booth
import VerifiedGarbage.Proof.Divstep.Tc32Words
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.RedRow
import VerifiedGarbage.Proof.Mont.X86.Row
import VerifiedGarbage.Proof.Mont.X86.Step
import VerifiedGarbage.Proof.P256.Point
import VerifiedGarbage.Proof.P256.Prime
import VerifiedGarbage.Proof.Rc2.Memory32
import VerifiedGarbage.Proof.Weierstrass.Cubic
import VerifiedGarbage.Proof.Weierstrass.GroupOrder
import VerifiedGarbage.Proof.Weierstrass.RcbIdent
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
import VerifiedGarbage.Proof.Weierstrass.X86.InvInit
import VerifiedGarbage.Proof.Weierstrass.X86.InvLinearMath
import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Proof.X25519.X86.Fold
import VerifiedGarbage.Proof.Divstep.Incl
import VerifiedGarbage.Proof.Divstep.Mred32
import VerifiedGarbage.Proof.Divstep.Red32
import VerifiedGarbage.Proof.Divstep.Tc32Red
import VerifiedGarbage.Proof.Divstep.Word32Bits
import VerifiedGarbage.Proof.Weierstrass.X86.InvRedSum
import VerifiedGarbage.Proof.Weierstrass.X86.InvRedWord
import VerifiedGarbage.Proof.Weierstrass.X86.Loop

/-! # P-256's group law, on x86 (32-bit) -/

public section

namespace VG.Proof.P256.X86

/-- P-256's group law, on x86 (32-bit), which the proofs of the curve's functions on this
target take. Not exposed: its importers need only its type, not the algebra
of its proof. -/
def hasLaw : Proof.Weierstrass.X86.Inv.HasLawInvOrd Spec.P256.curve :=
  { law := Proof.P256.law
    inv := fun hp => Proof.Weierstrass.X86.Inv.invSound_of_toM hp (Proof.Weierstrass.invToM_of_prime hp)
    prime := Proof.P256.primeOrder }

end VG.Proof.P256.X86
