module

public import VerifiedGarbage.Proof.Ecdsa.X86.CombCode
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombCode
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.X86.CombMain
import VerifiedGarbage.Proof.Ecdsa.X86.CombSign
import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
import VerifiedGarbage.Proof.Ecdsa.X86.Setup
import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.NativeTaint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.NativeHintData
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Mont.Words128
import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.P256Red
import VerifiedGarbage.Proof.Mont.X86.RedRow
import VerifiedGarbage.Proof.Mont.X86.Row
import VerifiedGarbage.Proof.Mont.X86.SparseShift
import VerifiedGarbage.Proof.Mont.X86.SparseStep
import VerifiedGarbage.Proof.Mont.X86.Step
import VerifiedGarbage.Proof.Rc2.Memory32
import VerifiedGarbage.Proof.Weierstrass.InvToM
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.Words32
import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed
import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
import VerifiedGarbage.Proof.Weierstrass.X86.Rep
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJ
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJSelect
import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Proof.X25519.X86.Fold
meta import VerifiedGarbage.Proof.Ecdsa.Sign
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombMain
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombSign
meta import VerifiedGarbage.Proof.Ecdsa.X86.Lays
meta import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
meta import VerifiedGarbage.Proof.Ecdsa.X86.Setup
meta import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.BitByte
meta import VerifiedGarbage.Proof.Framework.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Mont.Words128
meta import VerifiedGarbage.Proof.Mont.X86.Csub
meta import VerifiedGarbage.Proof.Mont.X86.Instr
meta import VerifiedGarbage.Proof.Mont.X86.P256Red
meta import VerifiedGarbage.Proof.Mont.X86.RedRow
meta import VerifiedGarbage.Proof.Mont.X86.Row
meta import VerifiedGarbage.Proof.Mont.X86.SparseShift
meta import VerifiedGarbage.Proof.Mont.X86.SparseStep
meta import VerifiedGarbage.Proof.Mont.X86.Step
meta import VerifiedGarbage.Proof.Rc2.Memory32
meta import VerifiedGarbage.Proof.Weierstrass.InvToM
meta import VerifiedGarbage.Proof.Weierstrass.TCombWords
meta import VerifiedGarbage.Proof.Weierstrass.Words32
meta import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
meta import VerifiedGarbage.Proof.Weierstrass.X86.Copy
meta import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
meta import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
meta import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
meta import VerifiedGarbage.Proof.Weierstrass.X86.Loop
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed
meta import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
meta import VerifiedGarbage.Proof.Weierstrass.X86.Rep
meta import VerifiedGarbage.Proof.Weierstrass.X86.TCombJ
meta import VerifiedGarbage.Proof.Weierstrass.X86.TCombJDigit
meta import VerifiedGarbage.Proof.Weierstrass.X86.TCombJSelect
meta import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne
meta import VerifiedGarbage.Proof.X25519.Field
meta import VerifiedGarbage.Proof.X25519.X86.Arith
meta import VerifiedGarbage.Proof.X25519.X86.Fold

/-!
# ECDSA over P-256 on x86 (32-bit): the constant time of the comb's last step
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

variable {scratchSecond : Bool}

/-- The last step's code. -/
def combFinish : Prog isa := .seq (.block p256K.outFix) (Impl.Weierstrass.X86.fprog p256K.F p256K.outOps)
materialize_code combFinish

theorem combFinish_rel : RelCT isa (VG.X86.Taint.Agree (combτAt scratchSecond))
    (.seq (.block p256K.outFix) (Impl.Weierstrass.X86.fprog p256K.F p256K.outOps)) (fun _ _ => True) := by
  change RelCT isa _ combFinish _
  cases scratchSecond <;>
    exact RelCT.taint (A := sseTaint) _ (fun _ _ h => h) (by native_taint_decide)

end VG.Proof.Ecdsa.X86
