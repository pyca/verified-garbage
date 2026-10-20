module

public import VerifiedGarbage.Impl.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Secret-independent traces of DSA comparison masks -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Dsa.X86 VG.Proof.Mont.X86.Dynamic

theorem lessThan_relCT (counter : Bool) (n a m : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint counter)) (lessThan n a m)
      (VG.X86.Taint.Agree (workspaceTaint counter)) :=
  erased_relCT _ (lessThan 1 0 0) (VG.Taint.hintOf taint (workspaceTaint counter) (Code.erase (lessThan 1 0 0)))
    rfl (by cases counter <;> rfl) (by cases counter <;> rfl) (by cases counter <;> rfl)

theorem nonzero_relCT (counter : Bool) (n a : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint counter)) (nonzero n a)
      (VG.X86.Taint.Agree (workspaceTaint counter)) :=
  erased_relCT _ (nonzero 1 0) (VG.Taint.hintOf taint (workspaceTaint counter) (Code.erase (nonzero 1 0)))
    rfl (by cases counter <;> rfl) (by cases counter <;> rfl) (by cases counter <;> rfl)

theorem equal_relCT (counter : Bool) (n a b : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint counter)) (equal n a b)
      (VG.X86.Taint.Agree (workspaceTaint counter)) :=
  erased_relCT _ (equal 1 0 0) (VG.Taint.hintOf taint (workspaceTaint counter) (Code.erase (equal 1 0 0)))
    rfl (by cases counter <;> rfl) (by cases counter <;> rfl) (by cases counter <;> rfl)

theorem checkRange_relCT (counter : Bool) (n a m flag : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint counter)) (checkRange n a m flag)
      (VG.X86.Taint.Agree (workspaceTaint counter)) :=
  erased_relCT _ (checkRange 1 0 0 0)
    (VG.Taint.hintOf taint (workspaceTaint counter) (Code.erase (checkRange 1 0 0 0)))
    rfl (by cases counter <;> rfl) (by cases counter <;> rfl) (by cases counter <;> rfl)

theorem checkZero_relCT (counter : Bool) (n a flag : Nat) (wantNonzero : Bool) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint counter)) (checkZero n a flag wantNonzero)
      (VG.X86.Taint.Agree (workspaceTaint counter)) := by
  cases wantNonzero
  · exact erased_relCT _ (checkZero 1 0 0 false)
      (VG.Taint.hintOf taint (workspaceTaint counter) (Code.erase (checkZero 1 0 0 false)))
      rfl (by cases counter <;> rfl) (by cases counter <;> rfl) (by cases counter <;> rfl)
  · exact erased_relCT _ (checkZero 1 0 0 true)
      (VG.Taint.hintOf taint (workspaceTaint counter) (Code.erase (checkZero 1 0 0 true)))
      rfl (by cases counter <;> rfl) (by cases counter <;> rfl) (by cases counter <;> rfl)

theorem andFlag_check (counter : Bool) (flag : Nat) :
    taint.checkBlock (workspaceTaint counter) (andFlag flag) = some (workspaceTaint counter) := by
  rw [← VG.X86.Taint.checkBlock_erase _ _ (by cases counter <;> rfl)]
  change taint.checkBlock (workspaceTaint counter) (KList.map Instr.erase (andFlag 0)) = _
  cases counter <;> rfl

end VG.Proof.Dsa.X86
