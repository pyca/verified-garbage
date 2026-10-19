module

import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafPointChecks
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafPointChecks
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafDigitChecks
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafDigitChecks
public import VerifiedGarbage.Proof.Weierstrass.X86.NafWindowTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86.NafWindowTiming
import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
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
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
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
import VerifiedGarbage.Proof.Weierstrass.X86.NafArithmeticTiming
import VerifiedGarbage.Proof.Weierstrass.X86.NafPoint
import VerifiedGarbage.Proof.Weierstrass.X86.NafPublicFields
import VerifiedGarbage.Proof.Weierstrass.X86.NafTableFields
import VerifiedGarbage.Proof.Weierstrass.X86.PointFieldTiming
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
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
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
meta import VerifiedGarbage.Proof.Weierstrass.X86.NafArithmeticTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86.NafPoint
meta import VerifiedGarbage.Proof.Weierstrass.X86.NafPublicFields
meta import VerifiedGarbage.Proof.Weierstrass.X86.NafTableFields
meta import VerifiedGarbage.Proof.Weierstrass.X86.PointFieldTiming
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
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Impl.Ecdsa.X86 VG.Proof.Weierstrass.X86 VG.Proof.Ecdsa.X86

def nafRunRead : Prog isa := .block (Naf.digitRead nafK)
materialize_code nafRunRead

theorem nafRunRead_ct : RegCT [.edi,.esi] nafRunRead :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafRunLookup : Prog isa := .block (Naf.publicEntry nafK)
materialize_code nafRunLookup

theorem nafRunLookup_ct : RegCT [.edi,.ebx] nafRunLookup :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafRunSign : Prog isa := .block [.alu .cmp .ebx (.imm 128)]
materialize_code nafRunSign

theorem nafRunSign_ct : RegCT [.ebx] nafRunSign :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafRunAbs : Prog isa := .block [.mov .eax (.imm 256),.alu .sub .eax (.reg .ebx),.mov .ebx (.reg .eax)]
materialize_code nafRunAbs

theorem nafRunAbs_ct : RegCT [.ebx] nafRunAbs :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafRunNeg : Prog isa := opCode p256Comb.SP (.sub nafK.E.y nafK.zero nafK.E.y)
materialize_code nafRunNeg

theorem nafRunNeg_ct : ScratchCT nafRunNeg :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

/-- The same copy as the table's step (`nafTableCopyStep`). -/
theorem nafRunCopy_ct : ScratchCT (.block (copyPt nafK.M.n nafK.R nafK.D)) :=
  nafTableCopyStep_ct

/-- The same doubling as the additions' (`nafAddDouble`). -/
theorem nafRunDouble_ct : ScratchCT (fprog p256Comb.SP (dblJMul nafK.S nafK.R nafK.D)) :=
  nafAddDouble_ct

def nafRunDec : Prog isa := .block [.alu .sub .esi (.imm 1)]
materialize_code nafRunDec

theorem nafRunDec_ct : RegCT [.esi] nafRunDec :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafRunTest : Prog isa := .block [.alu .test .esi (.reg .esi)]
materialize_code nafRunTest

theorem nafRunTest_ct : RegCT [.esi] nafRunTest :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafRunInfinity : Prog isa := .block (Jacobian.infinity nafK nafK.R)
materialize_code nafRunInfinity

theorem nafRunInfinity_ct : ScratchCT nafRunInfinity :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafRunInitCounter : Prog isa := .block [.mov .esi (.imm 256)]
materialize_code nafRunInitCounter

theorem nafRunInitCounter_ct : RegCT [.esi] nafRunInitCounter :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafRunFinish : Prog isa := Naf.finish nafK p256Comb.SP
materialize_code nafRunFinish

theorem nafRunFinish_ct : ScratchCT nafRunFinish :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

theorem nafWindow_checks : NafWindowChecks nafK p256Comb.SP :=
  ⟨nafTable_checks,
    ⟨⟨nafRunRead_ct,⟨nafRunLookup_ct,nafRunSign_ct,nafRunAbs_ct,nafRunNeg_ct⟩,
      nafDigitAdd_checks,nafRunCopy_ct⟩,nafRunDouble_ct,nafRunDec_ct,nafRunTest_ct⟩,
    nafRunInfinity_ct,nafRunInitCounter_ct,nafRunFinish_ct⟩

end VG.Proof.Ecdsa.Verify.X86
