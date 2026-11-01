module

public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Impl.Dsa.X86.Shape
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming

import VerifiedGarbage.Proof.Dsa.X86.ShapeInspectP
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86.ValidationBlocksTiming
import VerifiedGarbage.Proof.Dsa.X86.PointerTiming
import VerifiedGarbage.Proof.Dsa.X86.Pointer
import VerifiedGarbage.Proof.Framework.PlainSimp
/-! # Shape inspection traces do not depend on domain values -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/ShapeBlocksTiming.lean`, which only this module imported.
section

/-! # Fixed-address shape masks and digest clamping -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Mont.X86.Dynamic

theorem widthMask_relCT (n a tmp bits : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (widthMask n a tmp bits)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold widthMask
  refine RelCT.seq (lessThanConstant_relCT n a tmp _) ?_
  refine RelCT.seq (checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl) ?_
  split
  · exact RelCT.seq (lessThanConstant_relCT n a tmp _) (checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl)
  · exact checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl

theorem optionalWidth_relCT (n a tmp bits : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (optionalWidth n a tmp bits)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold optionalWidth
  split
  · exact widthMask_relCT n a tmp bits
  · exact checkedBlockInvariant (τ' := { workspaceTaint false with regs := .ofList [.edi, .edx] }) rfl rfl

theorem saveWidth_relCT (n bits output : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (Shape.saveWidth n bits output)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Shape.saveWidth
  refine RelCT.seq (optionalWidth_relCT n _ _ bits) (checkedBlockInvariant (τ' := workspaceTaint false) ?_ rfl)
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
  change taint.checkBlock (workspaceTaint false) [.store (sc 0) .edx] = _
  rfl

theorem threeWidths_relCT (n a b c output : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (Shape.threeWidths n a b c output)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  RelCT.seq (saveWidth_relCT n a output) (RelCT.seq (saveWidth_relCT n b (output + 4))
    (saveWidth_relCT n c (output + 8)))

theorem loadWidths_relCT (len a b c output : Nat) (modulus : VG.Impl.Dsa.Layout.Field) (base : Addr) (size : Nat)
    (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => VG.Proof.Mont.X86.Scr s base size ∧ VG.Proof.Mont.X86.Scr t base size ∧
      pointerValue base s (.input modulus) = pointerValue base t (.input modulus))
      (Shape.loadWidths len modulus a b c output) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Shape.loadWidths
  exact RelCT.seq (coreLoad_relCT _ len _ (.input modulus) base size hz)
    ((threeWidths_relCT _ a b c output).mono (fun _ _ h => taint.le_sound
      (show taint.le (workspaceTaint false) (workspaceTaint true) = true from rfl) h) (fun _ _ h => h))

theorem saveParity_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (.block (Shape.saveParity n))
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply checkedBlockInvariant (τ' := workspaceTaint false) ?_ rfl
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
  change taint.checkBlock (workspaceTaint false) [.mov .eax (.mem (sc 0)), .store (sc 0) .eax] = _
  rfl

theorem parity_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (.block (Shape.parity n))
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply checkedBlockInvariant (τ' := workspaceTaint false) ?_ rfl
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
  change taint.checkBlock (workspaceTaint false)
    [.mov .edx (.mem (sc 0)), .alu .and .edx (.mem (sc 0)), .alu .and .edx (.imm 0),
      .mov .eax (.imm 0), .alu .sub .eax (.reg .edx), .store (sc 0) .eax] = _
  rfl

theorem combine_relCT :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (.block Shape.combine)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl

theorem digestPrefix_relCT :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) Shape.digestPrefix
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl

end VG.Proof.Dsa.X86
end

end

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
