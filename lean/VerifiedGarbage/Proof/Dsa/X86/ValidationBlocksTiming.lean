module

public import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Dsa.X86.ChecksTiming
public import VerifiedGarbage.Impl.Dsa.X86.Validate

/-! # Constant-time validation masks and fixed constants -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Mont.X86.Dynamic

theorem setConst_relCT (n out value : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (.block (VG.Impl.Weierstrass.X86.setConst n out value)) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold VG.Impl.Weierstrass.X86.setConst
  apply blockFlatMap_relCT
  intro j
  apply checkedBlockInvariant (τ' := zeroTaint false) ?_ rfl
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
  change taint.checkBlock (workspaceTaint false) [.mov .eax (.imm 0), .store (sc 0) .eax] = _
  rfl

theorem lessThanConstant_relCT (n a tmp value : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (.block (lessThanConstant n a tmp value))
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold lessThanConstant
  exact RelCT.block_append (RelCT.seq (setConst_relCT n tmp value) (checkedBlockInvariant (lessThan_check n a tmp) rfl))

theorem lowerTwo_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (.block (Validate.lowerTwo n))
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Validate.lowerTwo
  rw [List.append_assoc]
  apply RelCT.block_append
  apply RelCT.seq (lessThanConstant_relCT n (slot n 5) (slot n 7) 2)
  apply RelCT.block_append
  exact RelCT.seq (checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl)
    (checkedBlockInvariant (andFlag_check _) rfl)

theorem rangeMask_relCT (n : Nat) (aboveOne : Bool) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (.block (checkRange n (slot n 5) (slot n 0) (Layout.field .mask) ++
        if aboveOne then Validate.lowerTwo n else [])) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply RelCT.block_append
  apply RelCT.seq (checkedBlockInvariant (checkRange_check _ _ _ _) rfl)
  cases aboveOne
  · exact RelCT.block_nil (fun _ _ h => h)
  · exact lowerTwo_relCT n

theorem equalMask_relCT (n a b : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (.block (equal n a b ++ Validate.accumulate)) (VG.X86.Taint.Agree (workspaceTaint false)) :=
  RelCT.block_append (RelCT.seq (checkedBlockInvariant (equal_check n a b) rfl)
    (checkedBlockInvariant (andFlag_check _) rfl))

theorem checkZero_relCT (n a flag : Nat) (wantNonzero : Bool) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (.block (checkZero n a flag wantNonzero))
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold checkZero
  rw [List.append_assoc]
  apply RelCT.block_append
  apply RelCT.seq (checkedBlockInvariant (nonzero_check n a) rfl)
  apply RelCT.block_append
  apply RelCT.seq (checkedBlockInvariant (τ' := workspaceTaint false) ?_ rfl)
    (checkedBlockInvariant (andFlag_check _) rfl)
  cases wantNonzero <;> rfl

theorem modulusMinus_relCT (n amount : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (.block (modulusMinus n amount))
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold modulusMinus
  apply RelCT.block_append
  apply RelCT.seq (setConst_relCT _ _ _)
  unfold chain
  apply blockFlatMap_relCT
  intro j
  split <;> apply checkedBlockInvariant (τ' := workspaceTaint false) ?_ rfl <;>
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
  · change taint.checkBlock (workspaceTaint false) [.mov .eax (.mem (sc 0)), .alu .sub .eax (.mem (sc 0)), .store (sc 0) .eax] = _
    rfl
  · change taint.checkBlock (workspaceTaint false) [.mov .eax (.mem (sc 0)), .alu .sbb .eax (.mem (sc 0)), .store (sc 0) .eax] = _
    rfl

end VG.Proof.Dsa.X86
