module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtLoadPBody
public import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayoutCT
public import VerifiedGarbage.Proof.Bignum.Arm.InputCompareLayoutCT
public import VerifiedGarbage.Proof.Bignum.Arm.MergeAcceptanceCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Secret CRT factor and coefficient loading is constant-time -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem crt_loadPBody_ct {base pp qp : BitVec 32} {len w k : Nat} {pb1 qb1 pb2 qb2 : List Byte} :
    RelCT isa (fun s t => CrtLoadPInput base pp qp len w k pb1 qb1 s ∧
      CrtLoadPInput base pp qp len w k pb2 qb2 t ∧ s.sp = t.sp) CrtFn.loadPBody (fun _ _ => True) := by
  let P := fun s t => CrtLoadPInput base pp qp len w k pb1 qb1 s ∧
    CrtLoadPInput base pp qp len w k pb2 qb2 t ∧ s.sp = t.sp
  let Q := fun (bs : List Byte) (s : State) => LayoutFrameReady base len w s ∧
    SavedOperand base qp len k 96 100 bs s ∧ 0 < k ∧ k ≤ 8 * w
  have firstCT : RelCT isa P (savedOperand 0 64 68) (fun _ _ => True) :=
    (savedOperandLayout_ct (by decide : 0 < 8)).mono
      (fun _ _ h => ⟨⟨h.1.ready, h.1.prime⟩, ⟨h.2.1.ready, h.2.1.prime⟩, h.2.2⟩) (fun _ _ _ => trivial)
  have firstWP (s : State) {pb qb : List Byte} (h : CrtLoadPInput base pp qp len w k pb qb s) :
      WP isa (savedOperand 0 64 68) s (Q qb) := by
    refine WP.mono (savedOperandLayout_ok s h.ready h.prime (by decide : 0 < 8) h.positive h.fits) ?_
    rintro t ⟨ready, _, _, frame, rest⟩
    exact ⟨ready, h.inverse.after_workspace frame rest, h.positive, h.fits⟩
  have first := (relCT_keep_sp firstCT (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨firstWP s h.1, firstWP t h.2.1⟩)
  have secondCT : RelCT isa (fun s t => s.sp = t.sp ∧ Q qb1 s ∧ Q qb2 t)
      (savedOperand 1 96 100) (fun _ _ => True) :=
    (savedOperandLayout_ct (by decide : 1 < 8)).mono
      (fun _ _ h => ⟨⟨h.2.1.1, h.2.1.2.1⟩, ⟨h.2.2.1, h.2.2.2.1⟩, h.1⟩) (fun _ _ _ => trivial)
  have secondWP (s : State) {qb : List Byte} (h : Q qb s) :
      WP isa (savedOperand 1 96 100) s (LayoutFrameReady base len w) :=
    WP.mono (savedOperandLayout_ok s h.1 h.2.1 (by decide : 1 < 8) h.2.2.1 h.2.2.2) (fun _ j => j.1)
  have second := (relCT_keep_sp secondCT (fun _ _ h => h.1)).wp
    (fun s t h => ⟨secondWP s h.2.1, secondWP t h.2.2⟩)
  have compare : RelCT isa (fun s t => s.sp = t.sp ∧ LayoutFrameReady base len w s ∧ LayoutFrameReady base len w t)
      inputCompare (fun _ _ => True) :=
    inputCompareLayout_ct.mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial)
  exact first.seq (second.seq ((relCT_keep_sp compare (fun _ _ h => h.1)).seq mergeAcceptance_ct))

end VG.Proof.Bignum.Arm
