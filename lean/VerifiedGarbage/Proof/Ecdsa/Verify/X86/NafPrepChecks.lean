module

public import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
public import VerifiedGarbage.Proof.Weierstrass.X86.NafPrepTiming
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import VerifiedGarbage.Impl.Ecdsa.Verify.X86
meta import VerifiedGarbage.Proof.Weierstrass.X86.NafPrepTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafLayout
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.WindowPrep
import VerifiedGarbage.Proof.Ecdsa.X86.Finish
import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Ecdsa.X86.Middle
import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
import VerifiedGarbage.Proof.Ecdsa.X86.Scalar
import VerifiedGarbage.Proof.Ecdsa.X86.Setup
import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
import VerifiedGarbage.Proof.Ecdsa.X86.Stages
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.TaintSym
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
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.Weierstrass.InvToM
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.Window5
import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
import VerifiedGarbage.Proof.Weierstrass.X86.JacAdd
import VerifiedGarbage.Proof.Weierstrass.X86.JacState
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed
import VerifiedGarbage.Proof.Weierstrass.X86.NafFinish
import VerifiedGarbage.Proof.Weierstrass.X86.NafPoint
import VerifiedGarbage.Proof.Weierstrass.X86.NafSum
import VerifiedGarbage.Proof.Weierstrass.X86.TComb
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJSelect
import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne
import VerifiedGarbage.Proof.Weierstrass.X86.WinEntry
import VerifiedGarbage.Proof.Weierstrass.X86.WinLoop
import VerifiedGarbage.Proof.Weierstrass.X86.WinSelect
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Proof.X25519.X86.Fold
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafLayout
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.WindowPrep
meta import VerifiedGarbage.Proof.Ecdsa.X86.Finish
meta import VerifiedGarbage.Proof.Ecdsa.X86.Lays
meta import VerifiedGarbage.Proof.Ecdsa.X86.Middle
meta import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
meta import VerifiedGarbage.Proof.Ecdsa.X86.Scalar
meta import VerifiedGarbage.Proof.Ecdsa.X86.Setup
meta import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
meta import VerifiedGarbage.Proof.Ecdsa.X86.Stages
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.BitByte
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Framework.X86.TaintSym
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
meta import VerifiedGarbage.Proof.Weierstrass.BytesLen
meta import VerifiedGarbage.Proof.Weierstrass.InvToM
meta import VerifiedGarbage.Proof.Weierstrass.TCombWords
meta import VerifiedGarbage.Proof.Weierstrass.Window5
meta import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
meta import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
meta import VerifiedGarbage.Proof.Weierstrass.X86.Copy
meta import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
meta import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
meta import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
meta import VerifiedGarbage.Proof.Weierstrass.X86.JacAdd
meta import VerifiedGarbage.Proof.Weierstrass.X86.JacState
meta import VerifiedGarbage.Proof.Weierstrass.X86.Loop
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed
meta import VerifiedGarbage.Proof.Weierstrass.X86.NafFinish
meta import VerifiedGarbage.Proof.Weierstrass.X86.NafPoint
meta import VerifiedGarbage.Proof.Weierstrass.X86.NafSum
meta import VerifiedGarbage.Proof.Weierstrass.X86.TComb
meta import VerifiedGarbage.Proof.Weierstrass.X86.TCombJDigit
meta import VerifiedGarbage.Proof.Weierstrass.X86.TCombJSelect
meta import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne
meta import VerifiedGarbage.Proof.Weierstrass.X86.WinEntry
meta import VerifiedGarbage.Proof.Weierstrass.X86.WinLoop
meta import VerifiedGarbage.Proof.Weierstrass.X86.WinSelect
meta import VerifiedGarbage.Proof.X25519.Field
meta import VerifiedGarbage.Proof.X25519.X86.Arith
meta import VerifiedGarbage.Proof.X25519.X86.Fold

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Impl.Ecdsa.Verify.X86 VG.Impl.Weierstrass.X86
open VG.Proof.Weierstrass.X86 VG.Proof.Ecdsa.X86

def nafPrepInitCode : Prog isa := .block (Naf.init (p256Comb.sl V) 3520)
def nafPrepStepCode : Prog isa := Naf.step 3580 3520
materialize_code nafPrepInitCode
materialize_code nafPrepStepCode

theorem nafPrep_checks : NafPrepChecks 3580 (p256Comb.sl V) 3520 := by
  refine ⟨?_,?_⟩
  · change ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (nafτ [.edi])) nafPrepInitCode
    exact Taint.constantTime (A:=taint) _ (fun _ _ _ _ h => h) (by taint_decide)
  · change ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (nafPrepτ 3520)) nafPrepStepCode
    exact Taint.constantTime (A:=taint) _ (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.Ecdsa.Verify.X86
