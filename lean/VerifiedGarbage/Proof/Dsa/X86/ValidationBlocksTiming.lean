module

import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.ChecksTiming
public import VerifiedGarbage.Impl.Dsa.X86.Validate
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Constant-time validation masks and fixed constants -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Mont.X86.Dynamic

theorem setConst_relCT (k out value : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (setConstW k out value)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold setConstW
  refine RelCT.seq (erased_relCT (σ := workspaceTaint false) _ (zerosW 0 1)
    (VG.Taint.hintOf taint (workspaceTaint false) (Code.erase (zerosW 0 1))) rfl rfl rfl rfl) ?_
  apply blockFlatMap_relCT
  intro j
  split
  · exact RelCT.block_nil (fun _ _ h => h)
  · apply checkedBlockInvariant (τ' := zeroTaint false) ?_ rfl
    rw [← VG.X86.Taint.checkBlock_erase _ _ rfl]
    change taint.checkBlock (workspaceTaint false) [.mov .eax (.imm 0), .store (sc 0) .eax] = _
    rfl

theorem lessThanConstant_relCT (n a tmp value : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (lessThanConstant n a tmp value)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  RelCT.seq (setConst_relCT _ tmp value) (lessThan_relCT false n a tmp)

theorem lowerTwo_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (Validate.lowerTwo n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Validate.lowerTwo
  refine RelCT.seq (lessThanConstant_relCT n (slot n 5) (slot n 7) 2) ?_
  exact erased_relCT _ (.block ([.alu .xor .eax (.imm (BitVec.allOnes 32)), .mov .edx (.reg .eax)] ++ andFlag 0))
    (.block []) rfl rfl rfl rfl

theorem rangeMask_relCT (n : Nat) (aboveOne : Bool) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (.seq (checkRange n (slot n 5) (slot n 0) (Layout.field .mask))
        (if aboveOne then Validate.lowerTwo n else .block [])) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply RelCT.seq (checkRange_relCT false _ _ _ _)
  cases aboveOne
  · exact RelCT.block_nil (fun _ _ h => h)
  · exact lowerTwo_relCT n

theorem equalMask_relCT (n a b : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (.seq (equal n a b) (.block Validate.accumulate)) (VG.X86.Taint.Agree (workspaceTaint false)) :=
  RelCT.seq (equal_relCT false n a b) (checkedBlockInvariant (andFlag_check false _) rfl)

theorem modulusMinus_relCT (n amount : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (modulusMinus n amount)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold modulusMinus
  refine RelCT.seq (setConst_relCT _ _ _) ?_
  exact erased_relCT _ (chainW .sbb 1 0 0 0)
    (VG.Taint.hintOf taint (workspaceTaint false) (Code.erase (chainW .sbb 1 0 0 0))) rfl rfl rfl rfl

end VG.Proof.Dsa.X86
