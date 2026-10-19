module

import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
public import VerifiedGarbage.Proof.Bignum.Arm.MontBodyCT
public import VerifiedGarbage.Impl.Bignum.Arm.MontFn
public import VerifiedGarbage.Spec.Rsa.Mont
meta import VerifiedGarbage.Impl.Bignum.Arm.MontFn
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Bignum.Arm.ArgsCT
import VerifiedGarbage.Proof.Bignum.Arm.BasesTail
import VerifiedGarbage.Proof.Bignum.Arm.CsubCT
import VerifiedGarbage.Proof.Bignum.Arm.CsubValue
import VerifiedGarbage.Proof.Bignum.Arm.FinishArgs
import VerifiedGarbage.Proof.Bignum.Arm.InitMetaMemory
import VerifiedGarbage.Proof.Bignum.Arm.LoadArray
import VerifiedGarbage.Proof.Bignum.Arm.MontBody
import VerifiedGarbage.Proof.Bignum.Arm.MontCore
import VerifiedGarbage.Proof.Bignum.Arm.MontFinish
import VerifiedGarbage.Proof.Bignum.Arm.MontInitCT
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Bignum.Arm.MontRounds
import VerifiedGarbage.Proof.Bignum.Arm.MontRoundsCT
import VerifiedGarbage.Proof.Bignum.Arm.PrepareZero
import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
import VerifiedGarbage.Proof.Bignum.Arm.ProductStage
import VerifiedGarbage.Proof.Bignum.Arm.QuotientStage
import VerifiedGarbage.Proof.Bignum.Arm.ReduceChoice
import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
import VerifiedGarbage.Proof.Bignum.Arm.ReductionStage
import VerifiedGarbage.Proof.Bignum.Arm.Round
import VerifiedGarbage.Proof.Bignum.Arm.RoundFinish
import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishMemory
import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishSteps
import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Bignum.Arm.RowAdvance
import VerifiedGarbage.Proof.Bignum.Arm.RowBody
import VerifiedGarbage.Proof.Bignum.Arm.RowBody2
import VerifiedGarbage.Proof.Bignum.Arm.RowCarry
import VerifiedGarbage.Proof.Bignum.Arm.RowCarryMemory
import VerifiedGarbage.Proof.Bignum.Arm.RowFull
import VerifiedGarbage.Proof.Bignum.Arm.RowFullCT
import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Bignum.Arm.SelectBody
import VerifiedGarbage.Proof.Bignum.Arm.SelectPrepare
import VerifiedGarbage.Proof.Bignum.Arm.SelectRow
import VerifiedGarbage.Proof.Bignum.Arm.SelectStep
import VerifiedGarbage.Proof.Bignum.Arm.SelectWord
import VerifiedGarbage.Proof.Bignum.Arm.Shift
import VerifiedGarbage.Proof.Bignum.Arm.ShiftArgs
import VerifiedGarbage.Proof.Bignum.Arm.ShiftCT
import VerifiedGarbage.Proof.Bignum.Arm.ShiftStep
import VerifiedGarbage.Proof.Bignum.Arm.Sub
import VerifiedGarbage.Proof.Bignum.Arm.SubAdvance
import VerifiedGarbage.Proof.Bignum.Arm.SubBody
import VerifiedGarbage.Proof.Bignum.Arm.SubRow
import VerifiedGarbage.Proof.Bignum.Arm.SubStep
import VerifiedGarbage.Proof.Bignum.Arm.WideMath
import VerifiedGarbage.Proof.Bignum.Arm.WideValue
import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Bignum.Arm.ZeroStep
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

/-! # The callable body reveals only the workspace, indices, and RSA word count -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt wordAt wOf numAt Layout Operand)

structure FnBodyReady (base : BitVec 32) (len w o a b : Nat) (s : State) : Prop where
  workspace : Workspace s base (8 * len)
  layout : Layout s.mem (State.addr base) len
  width : wOf s.mem (State.addr base) = w
  ptr : s.gpr .r0 = base
  outIndex : s.gpr .r2 = BitVec.ofNat 32 o
  aIndex : s.gpr .r3 = BitVec.ofNat 32 a
  bIndex : s.gpr .r12 = BitVec.ofNat 32 b
  inverse : ((word s.mem (State.addr base) (arrAt w 0)).toNat *
    (wordAt s.mem (State.addr base) Spec.Rsa.Mont.minvWord).toNat + 1) % 2 ^ 64 = 0
  operand : numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0

theorem bases_ready {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b)
    (s : State) (h : FnBodyReady base len w o a b s) :
    WP isa (.block MontFn.bases) s
      (InitReady base (8 * len) (arrAt w o) (arrAt w 3) (arrAt w a) (arrAt w b) (arrAt w 0) (arrAt w 2) (2 * w)) := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  obtain ⟨ctx, _⟩ := layout_context h.workspace hw fits ho ha hb
  have bound : 128 ≤ 8 * len := by
    simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at fits
    omega
  refine WP.mono (bases_ok s h.workspace bound header ho.1 ha.1 hb.1 h.ptr h.outIndex h.aIndex h.bIndex) ?_
  rintro t ⟨regs, mem, keep⟩
  refine ⟨ctx.congr keep.wr, ⟨_, regs, ?_⟩, ?_⟩
  · rw [mem]; exact native_inverse s.mem (State.addr base) (by omega) h.inverse
  · rw [mem, ← numAt_native, ← numAt_native]; exact h.operand

theorem montFnBody_ct {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b) (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t => FnBodyReady base len w o a b s ∧ FnBodyReady base len w o a b t)
      MontFn.body (fun _ _ => True) := by
  have ct : RelCT isa (fun s t => FnBodyReady base len w o a b s ∧ FnBodyReady base len w o a b t)
      (.block MontFn.bases) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r2, .r3, .r12]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.1.ptr.trans h.2.ptr.symm
    · exact h.1.outIndex.trans h.2.outIndex.symm
    · exact h.1.aIndex.trans h.2.aIndex.symm
    · exact h.1.bIndex.trans h.2.bIndex.symm
  exact (pair_posts ct (bases_ready ho ha hb)).seq (montBody_ct fit)

end VG.Proof.Bignum.Arm
