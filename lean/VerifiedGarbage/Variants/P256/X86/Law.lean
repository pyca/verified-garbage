module

import VerifiedGarbage.Proof.Weierstrass.X86.InvMain
public import VerifiedGarbage.Proof.Weierstrass.InvArith
public import VerifiedGarbage.Proof.P256.PrimeOrder
public import VerifiedGarbage.Proof.Weierstrass.X86.InvInterface
public import VerifiedGarbage.Proof.P256.Curve
public import Mathlib.Data.BitVec
public import VerifiedGarbage.Proof.Weierstrass.X86.InvMain
import VerifiedGarbage.Proof.Divstep.Bound
import VerifiedGarbage.Proof.Weierstrass.X86.InvBatch
import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.Weierstrass.Booth
public import VerifiedGarbage.Proof.Divstep.Tc32Words
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.X86.Mmx
public import VerifiedGarbage.Proof.Framework.X86.RegUpd
public import VerifiedGarbage.Proof.Mont.X86.Csub
public import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.X86.P256Red
public import VerifiedGarbage.Proof.Mont.X86.RedRow
public import VerifiedGarbage.Proof.Mont.X86.Row
public import VerifiedGarbage.Proof.Mont.X86.SparseShift
public import VerifiedGarbage.Proof.Mont.X86.SparseStep
public import VerifiedGarbage.Proof.Mont.X86.Step
public import VerifiedGarbage.Proof.P256.Point
public import VerifiedGarbage.Proof.P256.Prime
public import VerifiedGarbage.Proof.Rc2.Memory32
public import VerifiedGarbage.Proof.Weierstrass.Cubic
public import VerifiedGarbage.Proof.Weierstrass.GroupOrder
public import VerifiedGarbage.Proof.Weierstrass.RcbIdent
public import VerifiedGarbage.Proof.Weierstrass.X86.Copy
public import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
public import VerifiedGarbage.Proof.Weierstrass.X86.InvInit
public import VerifiedGarbage.Proof.Weierstrass.X86.InvLinearMath
public import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
public import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
public import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
public import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic
public import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed
public import VerifiedGarbage.Proof.X25519.Field
public import VerifiedGarbage.Proof.X25519.X86.Arith
public import VerifiedGarbage.Proof.X25519.X86.Fold
import VerifiedGarbage.Proof.Divstep.Incl
import VerifiedGarbage.Proof.Divstep.Mred32
import VerifiedGarbage.Proof.Divstep.Red32
import VerifiedGarbage.Proof.Divstep.Tc32Red
import VerifiedGarbage.Proof.Divstep.Tc32Words
import VerifiedGarbage.Proof.Divstep.Word32Bits
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
import VerifiedGarbage.Proof.Mont.X86.P256Red
import VerifiedGarbage.Proof.Mont.X86.RedRow
import VerifiedGarbage.Proof.Mont.X86.Row
import VerifiedGarbage.Proof.Mont.X86.SparseShift
import VerifiedGarbage.Proof.Mont.X86.SparseStep
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
import VerifiedGarbage.Proof.Weierstrass.X86.InvRedSum
import VerifiedGarbage.Proof.Weierstrass.X86.InvRedWord
import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Proof.X25519.X86.Fold

/-!
# P-256's group law, on x86 (32-bit)

The variant of `P256` on x86 (32-bit) (see `TCB/Emit.lean`): not an implementation
but the fact the proofs of P-256's functions take, `Proof.P256.law`, whose
proof needs Mathlib's algebra. Their registration files are generic over it
(`Generic/P256/X86/`, and `Generic/<Iface>/P256/X86/` for those generic over an
implementation too), so that this file alone, of those that emit them,
imports that algebra.
-/

@[expose] public section

namespace VG.Variants.P256.X86.Law

def variant : Proof.Weierstrass.X86.Inv.HasLawInvOrd Spec.P256.curve :=
  { law := Proof.P256.law
    inv := fun hp => Proof.Weierstrass.X86.Inv.invSound_of_toM hp (Proof.Weierstrass.invToM_of_prime hp)
    prime := Proof.P256.primeOrder }

end VG.Variants.P256.X86.Law
