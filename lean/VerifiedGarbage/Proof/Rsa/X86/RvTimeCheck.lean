module

public import VerifiedGarbage.Impl.Rsa.X86.RecoverRt
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Rsa.X86.RvTaint
meta import VerifiedGarbage.Impl.Rsa.X86.RecoverRt
meta import VerifiedGarbage.Proof.Rsa.X86.RvTaint
meta import VerifiedGarbage.Proof.Framework.X86.Taint

/-! # The taint checks of prime recovery at a run-time width

Every piece of the recovery without a call of `vg_rsa_mont_mul_at` leaks only
the arguments, `edi` and `esp` (`τA`); so do the blocks that push a call's
arguments, in its frame (`τF`).
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86
open VG.Impl.Rsa.X86.RecoverRt

theorem numbersCheck : (VG.Taint.check taint τA numbers (VG.Taint.hintOf taint τA numbers)).isSome = true := by
  taint_decide

theorem halfInitCheck : (VG.Taint.check taint τA halfInit (VG.Taint.hintOf taint τA halfInit)).isSome = true := by
  taint_decide

theorem halfBodyCheck : (VG.Taint.check taint τA halfBody (VG.Taint.hintOf taint τA halfBody)).isSome = true := by
  taint_decide

theorem montHeadCheck : (VG.Taint.check taint τA montHead (VG.Taint.hintOf taint τA montHead)).isSome = true := by
  taint_decide

theorem montTailCheck : (VG.Taint.check taint τA montTail (VG.Taint.hintOf taint τA montTail)).isSome = true := by
  taint_decide

theorem candInitCheck : (VG.Taint.check taint τA (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc VG.Impl.Rsa.X86.Recover.sCand) .eax]) (VG.Taint.hintOf taint τA (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc VG.Impl.Rsa.X86.Recover.sCand) .eax]))).isSome = true := by
  taint_decide

theorem alignStartCheck : (VG.Taint.check taint τA alignStart (VG.Taint.hintOf taint τA alignStart)).isSome = true := by
  taint_decide

theorem alignBodyCheck : (VG.Taint.check taint τA alignBody (VG.Taint.hintOf taint τA alignBody)).isSome = true := by
  taint_decide

theorem tableStartCheck : (VG.Taint.check taint τA tableStart (VG.Taint.hintOf taint τA tableStart)).isSome = true := by
  taint_decide

theorem windowCountCheck : (VG.Taint.check taint τA (.block VG.Impl.Rsa.X86.Recover.windowCount) (VG.Taint.hintOf taint τA (.block VG.Impl.Rsa.X86.Recover.windowCount))).isSome = true := by
  taint_decide

theorem windowNextCheck : (VG.Taint.check taint τA windowNext (VG.Taint.hintOf taint τA windowNext)).isSome = true := by
  taint_decide

theorem cntNextCheck : (VG.Taint.check taint τA (.block VG.Impl.Rsa.X86.Recover.cntNext) (VG.Taint.hintOf taint τA (.block VG.Impl.Rsa.X86.Recover.cntNext))).isSome = true := by
  taint_decide

theorem candSquareInitCheck : (VG.Taint.check taint τA candSquareInit (VG.Taint.hintOf taint τA candSquareInit)).isSome = true := by
  taint_decide

theorem sqTailCheck : (VG.Taint.check taint τA sqTail (VG.Taint.hintOf taint τA sqTail)).isSome = true := by
  taint_decide

theorem candNextCheck : (VG.Taint.check taint τA (.block VG.Impl.Rsa.X86.Recover.candNext) (VG.Taint.hintOf taint τA (.block VG.Impl.Rsa.X86.Recover.candNext))).isSome = true := by
  taint_decide

theorem finHeadCheck : (VG.Taint.check taint τA finHead (VG.Taint.hintOf taint τA finHead)).isSome = true := by
  taint_decide

theorem factorsCheck : (VG.Taint.check taint τA factors (VG.Taint.hintOf taint τA factors)).isSome = true := by
  taint_decide

theorem storesCheck : (VG.Taint.check taint τA stores (VG.Taint.hintOf taint τA stores)).isSome = true := by
  taint_decide

theorem tableCopy0Check : (VG.Taint.check taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (0 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (0 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy1Check : (VG.Taint.check taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (1 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (1 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy2Check : (VG.Taint.check taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (2 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (2 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy3Check : (VG.Taint.check taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (3 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (3 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy4Check : (VG.Taint.check taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (4 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (4 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy5Check : (VG.Taint.check taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (5 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (5 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy6Check : (VG.Taint.check taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (6 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (6 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy7Check : (VG.Taint.check taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (7 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (7 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy8Check : (VG.Taint.check taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (8 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (8 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy9Check : (VG.Taint.check taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (9 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (9 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy10Check : (VG.Taint.check taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (10 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (10 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy11Check : (VG.Taint.check taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (11 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (11 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy12Check : (VG.Taint.check taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (12 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (12 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy13Check : (VG.Taint.check taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (13 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf taint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (13 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem clrTop_mXmCheck : (VG.Taint.check taint τA (.block (clrTop VG.Impl.Rsa.X86.Recover.mXm)) (VG.Taint.hintOf taint τA (.block (clrTop VG.Impl.Rsa.X86.Recover.mXm)))).isSome = true := by
  taint_decide

theorem clrTop_mGCheck : (VG.Taint.check taint τA (.block (clrTop VG.Impl.Rsa.X86.Recover.mG)) (VG.Taint.hintOf taint τA (.block (clrTop VG.Impl.Rsa.X86.Recover.mG)))).isSome = true := by
  taint_decide

theorem clrTop_mYCheck : (VG.Taint.check taint τA (.block (clrTop VG.Impl.Rsa.X86.Recover.mY)) (VG.Taint.hintOf taint τA (.block (clrTop VG.Impl.Rsa.X86.Recover.mY)))).isSome = true := by
  taint_decide

theorem clrTop_mXCheck : (VG.Taint.check taint τA (.block (clrTop VG.Impl.Rsa.X86.Recover.mX)) (VG.Taint.hintOf taint τA (.block (clrTop VG.Impl.Rsa.X86.Recover.mX)))).isSome = true := by
  taint_decide

theorem mulArgs_mXm_mXm_mR2Check : (VG.Taint.check taint τF (.block (mulArgs VG.Impl.Rsa.X86.Recover.mXm VG.Impl.Rsa.X86.Recover.mXm VG.Impl.Rsa.X86.Recover.mR2)) (.block [])).isSome = true := by
  taint_decide

theorem mulArgs_mG_mG_mR2Check : (VG.Taint.check taint τF (.block (mulArgs VG.Impl.Rsa.X86.Recover.mG VG.Impl.Rsa.X86.Recover.mG VG.Impl.Rsa.X86.Recover.mR2)) (.block [])).isSome = true := by
  taint_decide

theorem mulArgs_mXm_mXm_mGCheck : (VG.Taint.check taint τF (.block (mulArgs VG.Impl.Rsa.X86.Recover.mXm VG.Impl.Rsa.X86.Recover.mXm VG.Impl.Rsa.X86.Recover.mG)) (.block [])).isSome = true := by
  taint_decide

theorem mulArgs_mY_mY_mYCheck : (VG.Taint.check taint τF (.block (mulArgs VG.Impl.Rsa.X86.Recover.mY VG.Impl.Rsa.X86.Recover.mY VG.Impl.Rsa.X86.Recover.mY)) (.block [])).isSome = true := by
  taint_decide

theorem mulArgs_mY_mY_mXmCheck : (VG.Taint.check taint τF (.block (mulArgs VG.Impl.Rsa.X86.Recover.mY VG.Impl.Rsa.X86.Recover.mY VG.Impl.Rsa.X86.Recover.mXm)) (.block [])).isSome = true := by
  taint_decide

theorem mulArgs_mX_mY_mYCheck : (VG.Taint.check taint τF (.block (mulArgs VG.Impl.Rsa.X86.Recover.mX VG.Impl.Rsa.X86.Recover.mY VG.Impl.Rsa.X86.Recover.mY)) (.block [])).isSome = true := by
  taint_decide

end VG.Proof.Rsa.X86.Recover
