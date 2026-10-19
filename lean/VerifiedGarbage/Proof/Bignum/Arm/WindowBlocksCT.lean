module

import VerifiedGarbage.Proof.Bignum.Arm.StackCT
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Bignum.Arm.WindowExp
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.Bignum.Arm.WindowExp
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Bignum.Arm.AddCarry
import VerifiedGarbage.Proof.Bignum.Arm.ArgsCT
import VerifiedGarbage.Proof.Bignum.Arm.BasesTail
import VerifiedGarbage.Proof.Bignum.Arm.CsubCT
import VerifiedGarbage.Proof.Bignum.Arm.CsubValue
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopSteps
import VerifiedGarbage.Proof.Bignum.Arm.ExpBit
import VerifiedGarbage.Proof.Bignum.Arm.ExpBitTest
import VerifiedGarbage.Proof.Bignum.Arm.ExpBitsCT
import VerifiedGarbage.Proof.Bignum.Arm.ExpByte
import VerifiedGarbage.Proof.Bignum.Arm.ExpByteHead
import VerifiedGarbage.Proof.Bignum.Arm.ExpByteHeadCT
import VerifiedGarbage.Proof.Bignum.Arm.ExpByteLoad
import VerifiedGarbage.Proof.Bignum.Arm.ExpByteNext
import VerifiedGarbage.Proof.Bignum.Arm.ExpByteSave
import VerifiedGarbage.Proof.Bignum.Arm.ExpBytes
import VerifiedGarbage.Proof.Bignum.Arm.ExpControl
import VerifiedGarbage.Proof.Bignum.Arm.ExpInit
import VerifiedGarbage.Proof.Bignum.Arm.ExpRound
import VerifiedGarbage.Proof.Bignum.Arm.ExpRoundCT
import VerifiedGarbage.Proof.Bignum.Arm.ExpStep
import VerifiedGarbage.Proof.Bignum.Arm.ExpStepCT
import VerifiedGarbage.Proof.Bignum.Arm.FinishArgs
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.HeaderStore
import VerifiedGarbage.Proof.Bignum.Arm.InitMetaMemory
import VerifiedGarbage.Proof.Bignum.Arm.KeepsBridge
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
import VerifiedGarbage.Proof.Bignum.Arm.LoadArray
import VerifiedGarbage.Proof.Bignum.Arm.MontBody
import VerifiedGarbage.Proof.Bignum.Arm.MontCore
import VerifiedGarbage.Proof.Bignum.Arm.MontFinish
import VerifiedGarbage.Proof.Bignum.Arm.MontFnBody
import VerifiedGarbage.Proof.Bignum.Arm.MontInitCT
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.MontOpArgs
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.Bignum.Arm.MontRounds
import VerifiedGarbage.Proof.Bignum.Arm.MontRoundsCT
import VerifiedGarbage.Proof.Bignum.Arm.PrepareZero
import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
import VerifiedGarbage.Proof.Bignum.Arm.ProductStage
import VerifiedGarbage.Proof.Bignum.Arm.QuotientStage
import VerifiedGarbage.Proof.Bignum.Arm.ReduceChoice
import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
import VerifiedGarbage.Proof.Bignum.Arm.ReductionStage
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
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
import VerifiedGarbage.Proof.Bignum.Arm.RowLoopCT
import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasBody
import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasRow
import VerifiedGarbage.Proof.Bignum.Arm.SelectArray
import VerifiedGarbage.Proof.Bignum.Arm.SelectArrayArgs
import VerifiedGarbage.Proof.Bignum.Arm.SelectBody
import VerifiedGarbage.Proof.Bignum.Arm.SelectPrepare
import VerifiedGarbage.Proof.Bignum.Arm.SelectRow
import VerifiedGarbage.Proof.Bignum.Arm.SelectStep
import VerifiedGarbage.Proof.Bignum.Arm.SelectWord
import VerifiedGarbage.Proof.Bignum.Arm.SetSmall
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallArgs
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.Shift
import VerifiedGarbage.Proof.Bignum.Arm.ShiftArgs
import VerifiedGarbage.Proof.Bignum.Arm.ShiftCT
import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeft
import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeftCT
import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeftStep
import VerifiedGarbage.Proof.Bignum.Arm.ShiftStep
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.SquareBody
import VerifiedGarbage.Proof.Bignum.Arm.SquareCross
import VerifiedGarbage.Proof.Bignum.Arm.SquareFinish
import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
import VerifiedGarbage.Proof.Bignum.Arm.SquareOpCT
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.Sub
import VerifiedGarbage.Proof.Bignum.Arm.SubAdvance
import VerifiedGarbage.Proof.Bignum.Arm.SubBody
import VerifiedGarbage.Proof.Bignum.Arm.SubRow
import VerifiedGarbage.Proof.Bignum.Arm.SubStep
import VerifiedGarbage.Proof.Bignum.Arm.WideMath
import VerifiedGarbage.Proof.Bignum.Arm.WideValue
import VerifiedGarbage.Proof.Bignum.Arm.WindowBytes
import VerifiedGarbage.Proof.Bignum.Arm.WindowCtl
import VerifiedGarbage.Proof.Bignum.Arm.WindowPhase
import VerifiedGarbage.Proof.Bignum.Arm.WindowScan
import VerifiedGarbage.Proof.Bignum.Arm.WindowSelect
import VerifiedGarbage.Proof.Bignum.Arm.WindowState
import VerifiedGarbage.Proof.Bignum.Arm.ZeroStep
import VerifiedGarbage.Proof.Bignum.FoldedPublic
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

/-! # The control blocks of the windowed exponentiation leak only the workspace pointer

Each block's addresses are the workspace pointer `r0` plus constants. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

/-- Two runs of `a` then `b` from states each satisfying its own
precondition, with the same stack pointer. -/
theorem relCT_chain {P₁ P₂ Q₁ Q₂ : State → Prop} {a b : Prog isa}
    (ha : RelCT isa (fun s t => P₁ s ∧ P₂ t ∧ s.sp = t.sp) a (fun _ _ => True))
    (wa₁ : ∀ s, P₁ s → WP isa a s Q₁) (wa₂ : ∀ s, P₂ s → WP isa a s Q₂)
    (hb : RelCT isa (fun s t => Q₁ s ∧ Q₂ t ∧ s.sp = t.sp) b (fun _ _ => True)) :
    RelCT isa (fun s t => P₁ s ∧ P₂ t ∧ s.sp = t.sp) (.seq a b) (fun _ _ => True) :=
  ((relCT_keep_sp ha (fun _ _ h => h.2.2)).wp (fun s t h => ⟨wa₁ s h.1, wa₂ t h.2.1⟩)).seq
    (hb.mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h))

theorem r0_agree {s t : State} (h : s.gpr .r0 = t.gpr .r0) : taint.Agree (Taint.ofRegs [.r0]) s t := by
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h

theorem tableInit_ct : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block tableInit) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => r0_agree h) (by taint_decide)

theorem entryNext_ct : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block entryNext) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => r0_agree h) (by taint_decide)

theorem entryCopyArgs_ct (a : Nat) (ha : a < 8) :
    RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block (entryCopyArgs a)) (fun _ _ => True) := by
  have : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => r0_agree h) (by taint_decide)

theorem scanHead_ct :
    RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block (scanBit ++ scanArgs)) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => r0_agree h) (by taint_decide)

theorem windowReset_ct : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block windowReset) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => r0_agree h) (by taint_decide)

theorem windowBitValue_ct :
    RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block windowBitValue) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => r0_agree h) (by taint_decide)

theorem setBit_ct : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block [.mov .r11 (.imm 1)])
    (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => r0_agree h) (by taint_decide)

theorem expShift_ct : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block expShift) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => r0_agree h) (by taint_decide)

theorem expDecrement_ct : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block expDecrement) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => r0_agree h) (by taint_decide)

theorem expByteNext_ct : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block expByteNext) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => r0_agree h) (by taint_decide)

end VG.Proof.Bignum.Arm
