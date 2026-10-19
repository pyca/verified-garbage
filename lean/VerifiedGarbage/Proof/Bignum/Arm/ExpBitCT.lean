module
public import VerifiedGarbage.Impl.Bignum.Arm.Exp
public import VerifiedGarbage.Proof.Bignum.Arm.ExpState
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.ExpStepCT
meta import VerifiedGarbage.Impl.Bignum.Arm.Exp
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Bignum.Arm.ExpStep
import VerifiedGarbage.Proof.Bignum.Arm.ExpBitTest
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Arm.AddCarry
import VerifiedGarbage.Proof.Bignum.Arm.ArgsCT
import VerifiedGarbage.Proof.Bignum.Arm.BasesTail
import VerifiedGarbage.Proof.Bignum.Arm.CsubCT
import VerifiedGarbage.Proof.Bignum.Arm.CsubValue
import VerifiedGarbage.Proof.Bignum.Arm.ExpBit
import VerifiedGarbage.Proof.Bignum.Arm.FinishArgs
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.HeaderStore
import VerifiedGarbage.Proof.Bignum.Arm.InitMetaMemory
import VerifiedGarbage.Proof.Bignum.Arm.KeepsBridge
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
import VerifiedGarbage.Proof.Bignum.Arm.ZeroStep
import VerifiedGarbage.Proof.Bignum.FoldedPublic
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

/-! # Only the public exponent bit controls a branch -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (arrAt)

structure ExpBitInput (base : BitVec 32) (len w M x E V : Nat) (s : State) : Prop where
  power : ExpState base len w M x E s
  byte : s.mem.readW (VG.Proof.Mont.off (State.addr base) 200) 32 = BitVec.ofNat 32 V

theorem ExpBitInput.square (s : State) {base : BitVec 32} {len w M x E V : Nat}
    (h : ExpBitInput base len w M x E V s) : WP isa (squareOp 6 6) s (ExpBitInput base len w M x (2 * E) V) := by
  refine WP.mono (exp_square_ok s h.power) ?_
  rintro t ⟨power, keeps, _, _⟩
  have size : 256 ≤ 8 * len := by
    have := h.power.ready.layout.2.2.1
    simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at this
    omega
  exact ⟨power, (keeps_header_readW keeps size (d := 200) (bits := 32) (by decide)).trans h.byte⟩

theorem ExpBitInput.test (s : State) {base : BitVec 32} {len w M x E V : Nat}
    (h : ExpBitInput base len w M x E V s) (hv : V < 2 ^ 32) :
    WP isa (.block expBitTest) s fun t => ExpState base len w M x E t ∧ t.z = decide (V / 128 % 2 = 0) := by
  have size : 204 ≤ 8 * len := by
    have := h.power.ready.layout.2.2.1
    simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at this
    omega
  refine WP.mono (expBitTest_ok s h.power.ready.workspace size h.power.ready.ptr hv h.byte) ?_
  rintro t ⟨zero, mem, rest⟩
  exact ⟨h.power.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.power.ready.ptr), zero⟩

theorem expBit_ct {base : BitVec 32} {len w M1 M2 x1 x2 E V : Nat}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (hv : V < 2 ^ 32) :
    RelCT isa (fun s t => ExpBitInput base len w M1 x1 E V s ∧
      ExpBitInput base len w M2 x2 E V t ∧ s.sp = t.sp) expBit (fun _ _ => True) := by
  let P := fun (s t : State) => ExpBitInput base len w M1 x1 E V s ∧
    ExpBitInput base len w M2 x2 E V t ∧ s.sp = t.sp
  have square := (relCT_keep_sp ((exp_square_ct (len := len) (w := w)).mono (P' := P)
    (fun _ _ h => ⟨h.1.power, h.2.1.power, h.2.2⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨h.1.square s, h.2.1.square t⟩)
  let Q := fun (s t : State) => s.sp = t.sp ∧ ExpBitInput base len w M1 x1 (2 * E) V s ∧
    ExpBitInput base len w M2 x2 (2 * E) V t
  have test : RelCT isa Q (.block expBitTest) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.2.1.power.ready.ptr.trans h.2.2.power.ready.ptr.symm
  have tested := (relCT_keep_sp test (fun _ _ h => h.1)).wp
    (fun s t h => ⟨h.2.1.test s hv, h.2.2.test t hv⟩)
  refine square.seq (tested.seq (RelCT.ite ?_ ?_ ?_))
  · intro s t h
    change some (!s.z) = some (!t.z)
    rw [h.2.1.2, h.2.2.2]
  · apply (exp_multiply_ct (base := base) (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2) (E := 2 * E) fit).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1, h.1.1⟩) (fun _ _ h => h)
  · exact RelCT.block_nil (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
