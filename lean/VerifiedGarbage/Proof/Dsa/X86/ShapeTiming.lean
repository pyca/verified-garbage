module
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Impl.Dsa.X86.Shape
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming

import VerifiedGarbage.Proof.Dsa.X86.ShapeBlocksTiming
import VerifiedGarbage.Proof.Dsa.X86.ShapeInspectP
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Shape inspection traces do not depend on domain values -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem inspectP_relCT (len : Nat) (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      pointerValue base s (.input .p) = pointerValue base t (.input .p))
      (Shape.inspectP len) (VG.X86.Taint.Agree (workspaceTaint false)) :=
  RelCT.seq (loadWidths_relCT len 1024 2048 3072 32 .p base size hz) (saveParity_relCT _)

theorem inspectQ_relCT (len : Nat) (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      pointerValue base s (.input .q) = pointerValue base t (.input .q))
      (Shape.inspectQ len) (VG.X86.Taint.Agree (workspaceTaint false)) :=
  RelCT.seq (loadWidths_relCT len 160 224 256 44 .q base size hz)
    (RelCT.block_append (RelCT.seq (parity_relCT _) combine_relCT))

theorem shape_relCT (pLen qLen : Nat) (base : Addr) (size : Nat)
    (hz : Layout.saved ≤ size) (h4 : 4 ≤ pLen) (hmax : pLen ≤ 384) (hw4 : pLen % 4 = 0) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      OperandReady s base 48 (.input .p) pLen ∧ OperandReady t base 48 (.input .p) pLen ∧
      pointerValue base s (.input .p) = pointerValue base t (.input .p) ∧
      pointerValue base s (.input .q) = pointerValue base t (.input .q))
      (Shape.check pLen qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Shape.check Core.sequence
  dsimp only [List.foldr]
  refine RelCT.seq (M := isa) (R := fun s t => Scr s base size ∧ Scr t base size ∧
    pointerValue base s (.input .q) = pointerValue base t (.input .q)) ?_ ?_
  · intro s t tr ur sf tf ⟨S, T, A, B, P, Q⟩ E F
    have trace := (inspectP_relCT pLen base size hz _ _ _ _ _ _ ⟨S, T, P⟩ E F).1
    obtain ⟨_, _, _, _, K1, O1⟩ := wp_result (inspectP_ok S hz h4 hmax hw4 A rfl) E
    obtain ⟨_, _, _, _, K2, O2⟩ := wp_result (inspectP_ok T hz h4 hmax hw4 B rfl) F
    have P1 := pointerValue_keep K1 (by decide) O1 (by decide : contextBytes 48 ≤ 8192) (.input .q)
    have P2 := pointerValue_keep K2 (by decide) O2 (by decide : contextBytes 48 ≤ 8192) (.input .q)
    exact ⟨trace, S.of_keeps K1 (by decide), T.of_keeps K2 (by decide), P1.trans (Q.trans P2.symm)⟩
  · exact RelCT.seq (inspectQ_relCT qLen base size hz)
      (RelCT.seq digestPrefix_relCT (RelCT.seq
        (checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl) (RelCT.block_nil (fun _ _ h => h))))

end VG.Proof.Dsa.X86
