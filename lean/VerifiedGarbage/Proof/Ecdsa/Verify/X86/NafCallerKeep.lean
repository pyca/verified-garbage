module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafCallerInput
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafCallerInput
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombTailCT
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombTailCT
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafMul
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafMul
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Points
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Points
import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.X86.Peer
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombInput
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombMain
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombStagesCT
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Final
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafLayout
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafMulSetup
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafMulTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.WindowPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.WindowPrep
import VerifiedGarbage.Proof.Ecdsa.X86.CombCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombMain
import VerifiedGarbage.Proof.Ecdsa.X86.CombSign
import VerifiedGarbage.Proof.Ecdsa.X86.Finish
import VerifiedGarbage.Proof.Ecdsa.X86.Inv
import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Ecdsa.X86.Middle
import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
import VerifiedGarbage.Proof.Ecdsa.X86.Scalar
import VerifiedGarbage.Proof.Ecdsa.X86.Setup
import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
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
import VerifiedGarbage.Proof.Weierstrass.X86.FprogJ
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
import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
import VerifiedGarbage.Proof.Weierstrass.X86.PointFieldTiming
import VerifiedGarbage.Proof.Weierstrass.X86.Rep
import VerifiedGarbage.Proof.Weierstrass.X86.ScalarPower
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJ
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJEntry
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJSelect
import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne
import VerifiedGarbage.Proof.Weierstrass.X86.WinEntry
import VerifiedGarbage.Proof.Weierstrass.X86.WinLoop
import VerifiedGarbage.Proof.Weierstrass.X86.WinSelect
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Proof.X25519.X86.Fold
meta import VerifiedGarbage.Proof.EcKey.PublicKey
meta import VerifiedGarbage.Proof.Ecdh.X86.Peer
meta import VerifiedGarbage.Proof.Ecdsa.Sign
meta import VerifiedGarbage.Proof.Ecdsa.Verify
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombInput
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombMain
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombPoints
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombStagesCT
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Final
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafLayout
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafMulSetup
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafMulTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.WindowPoints
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.WindowPrep
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombMain
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombSign
meta import VerifiedGarbage.Proof.Ecdsa.X86.Finish
meta import VerifiedGarbage.Proof.Ecdsa.X86.Inv
meta import VerifiedGarbage.Proof.Ecdsa.X86.Lays
meta import VerifiedGarbage.Proof.Ecdsa.X86.Middle
meta import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
meta import VerifiedGarbage.Proof.Ecdsa.X86.Scalar
meta import VerifiedGarbage.Proof.Ecdsa.X86.Setup
meta import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.BitByte
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
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
meta import VerifiedGarbage.Proof.Weierstrass.X86.FprogJ
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
meta import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
meta import VerifiedGarbage.Proof.Weierstrass.X86.PointFieldTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86.Rep
meta import VerifiedGarbage.Proof.Weierstrass.X86.ScalarPower
meta import VerifiedGarbage.Proof.Weierstrass.X86.TCombJ
meta import VerifiedGarbage.Proof.Weierstrass.X86.TCombJDigit
meta import VerifiedGarbage.Proof.Weierstrass.X86.TCombJEntry
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
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Impl.Ecdsa.Verify.X86
open VG.Impl.Ecdh.X86 (PX PY)
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Ecdsa.X86 VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass
open Spec.Weierstrass

def vNafCode : Prog isa := Cfg.windowMulQ p256Comb
materialize_code vNafCode

theorem vSave_sp : SpOk vSaveCode p256Comb.stk := ⟨NoSp.of_all (by lit_decide),by lit_decide⟩
theorem vNaf_sp : SpOk vNafCode p256Comb.stk := ⟨NoSp.of_all (by lit_decide),by lit_decide⟩

theorem vSave_input (hc : CfgOk p256Comb) {s₀ s : State} {base : Addr}
    (h : VPointInput s₀ base s) : WP isa vSaveCode s (VPointInput s₀ base) := by
  refine h.1.withSp vSave_sp (WP.mono (save_ok hc h.1.scr) (fun t ⟨st,kt,ut,_⟩ ft => ?_))
  refine ⟨⟨st,(kt.gpr _ (by decide)).trans h.1.esp,kt.rd.trans h.1.rd,kt.wr.trans h.1.wr,
    h.1.fixed.unch hc.n10 h.1.scr.nowrap (fixedOk_slW (by decide)) ut,ft,h.1.sp_lo⟩,?_⟩
  apply h.2.transfer
  intro i hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl <;>
    exact sv_unch ut hc.n10 h.1.scr.nowrap (by decide) (apart_slW (by decide))

theorem vNaf_keep (hc : CfgOk p256Comb) (hC : Law p256Comb.C) (ha : AM3 p256Comb.C)
    {s₀ s : State} {base : Addr} (h : VPointInput s₀ base s) :
    WP isa vNafCode s (Keep p256Comb s₀ base) := by
  have hi := vPointInput_naf hc hC h
  refine h.1.withSp vNaf_sp (WP.mono (windowMulQ_ok hc rfl hC ha h.1.scr h.1.fixed
    (Ecdh.X86.peerPt_onCurve hc _ _ _) hi.px_lt hi.py_lt hi.point) (fun t ⟨kt,ut,_⟩ ft => ?_))
  exact ⟨h.1.scr.of_keeps kt (by decide),(kt.gpr _ (by decide)).trans h.1.esp,
    kt.rd.trans h.1.rd,kt.wr.trans h.1.wr,
    h.1.fixed.unch hc.n10 h.1.scr.nowrap (windowW_fixed rfl) ut,ft,h.1.sp_lo⟩

end VG.Proof.Ecdsa.Verify.X86
