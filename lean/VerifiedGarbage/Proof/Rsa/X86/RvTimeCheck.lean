module

public import VerifiedGarbage.Impl.Rsa.X86.RecoverRt
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Rsa.X86.RvTaint
meta import VerifiedGarbage.Impl.Rsa.X86.RecoverRt
meta import VerifiedGarbage.Proof.Rsa.X86.RvTaint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-! # The taint checks of prime recovery at a run-time width

Every piece of the recovery without a call of `vg_rsa_mont_mul_at` leaks only
the arguments, `edi` and `esp` (`τA`); so do the blocks that push a call's
arguments, in its frame (`τF`).
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86
open VG.Impl.Rsa.X86.RecoverRt

theorem nilCheck : (VG.Taint.check sseTaint τA (.block []) (VG.Taint.hintOf sseTaint τA (.block []))).isSome = true := by
  taint_decide

theorem numbersCheck : ∃ hint, (VG.Taint.check sseTaint τA numbers hint).isSome = true := ⟨_, by taint_decide⟩

theorem halfInitCheck : (VG.Taint.check sseTaint τA halfInit (VG.Taint.hintOf sseTaint τA halfInit)).isSome = true := by
  taint_decide

theorem halfBodyCheck : ∃ hint, (VG.Taint.check sseTaint τA halfBody hint).isSome = true := ⟨_, by taint_decide⟩

theorem montHeadCheck : ∃ hint, (VG.Taint.check sseTaint τA montHead hint).isSome = true := ⟨_, by taint_decide⟩

theorem montTailCheck : ∃ hint, (VG.Taint.check sseTaint τA montTail hint).isSome = true := ⟨_, by taint_decide⟩

theorem candInitCheck : (VG.Taint.check sseTaint τA (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc VG.Impl.Rsa.X86.Recover.sCand) .eax]) (VG.Taint.hintOf sseTaint τA (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc VG.Impl.Rsa.X86.Recover.sCand) .eax]))).isSome = true := by
  taint_decide

theorem alignStartCheck : ∃ hint, (VG.Taint.check sseTaint τA alignStart hint).isSome = true := ⟨_, by taint_decide⟩

theorem alignBodyCheck : (VG.Taint.check sseTaint τA alignBody (VG.Taint.hintOf sseTaint τA alignBody)).isSome = true := by
  taint_decide

theorem tableStartCheck : (VG.Taint.check sseTaint τA tableStart (VG.Taint.hintOf sseTaint τA tableStart)).isSome = true := by
  taint_decide

theorem windowCountCheck : (VG.Taint.check sseTaint τA (.block VG.Impl.Rsa.X86.Recover.windowCount) (VG.Taint.hintOf sseTaint τA (.block VG.Impl.Rsa.X86.Recover.windowCount))).isSome = true := by
  taint_decide

theorem windowNextCheck : ∃ hint, (VG.Taint.check sseTaint τA windowNext hint).isSome = true := ⟨_, by taint_decide⟩

theorem cntNextCheck : (VG.Taint.check sseTaint τA (.block VG.Impl.Rsa.X86.Recover.cntNext) (VG.Taint.hintOf sseTaint τA (.block VG.Impl.Rsa.X86.Recover.cntNext))).isSome = true := by
  taint_decide

theorem candSquareInitCheck : (VG.Taint.check sseTaint τA candSquareInit (VG.Taint.hintOf sseTaint τA candSquareInit)).isSome = true := by
  taint_decide

theorem sqTailCheck : (VG.Taint.check sseTaint τA sqTail (VG.Taint.hintOf sseTaint τA sqTail)).isSome = true := by
  taint_decide

theorem candNextCheck : (VG.Taint.check sseTaint τA (.block VG.Impl.Rsa.X86.Recover.candNext) (VG.Taint.hintOf sseTaint τA (.block VG.Impl.Rsa.X86.Recover.candNext))).isSome = true := by
  taint_decide

theorem finHeadCheck : (VG.Taint.check sseTaint τA finHead (VG.Taint.hintOf sseTaint τA finHead)).isSome = true := by
  taint_decide

theorem storesCheck : (VG.Taint.check sseTaint τA stores (VG.Taint.hintOf sseTaint τA stores)).isSome = true := by
  taint_decide

theorem tableCopy0Check : (VG.Taint.check sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (0 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (0 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy1Check : (VG.Taint.check sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (1 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (1 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy2Check : (VG.Taint.check sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (2 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (2 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy3Check : (VG.Taint.check sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (3 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (3 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy4Check : (VG.Taint.check sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (4 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (4 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy5Check : (VG.Taint.check sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (5 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (5 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy6Check : (VG.Taint.check sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (6 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (6 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy7Check : (VG.Taint.check sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (7 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (7 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy8Check : (VG.Taint.check sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (8 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (8 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy9Check : (VG.Taint.check sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (9 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (9 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy10Check : (VG.Taint.check sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (10 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (10 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy11Check : (VG.Taint.check sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (11 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (11 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy12Check : (VG.Taint.check sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (12 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (12 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem tableCopy13Check : (VG.Taint.check sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (13 + 2) VG.Impl.Rsa.X86.Recover.mXm) (VG.Taint.hintOf sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy nar (13 + 2) VG.Impl.Rsa.X86.Recover.mXm))).isSome = true := by
  taint_decide

theorem clrTop_mXmCheck : (VG.Taint.check sseTaint τA (.block (clrTop VG.Impl.Rsa.X86.Recover.mXm)) (VG.Taint.hintOf sseTaint τA (.block (clrTop VG.Impl.Rsa.X86.Recover.mXm)))).isSome = true := by
  taint_decide

theorem clrTop_mGCheck : (VG.Taint.check sseTaint τA (.block (clrTop VG.Impl.Rsa.X86.Recover.mG)) (VG.Taint.hintOf sseTaint τA (.block (clrTop VG.Impl.Rsa.X86.Recover.mG)))).isSome = true := by
  taint_decide

theorem clrTop_mYCheck : (VG.Taint.check sseTaint τA (.block (clrTop VG.Impl.Rsa.X86.Recover.mY)) (VG.Taint.hintOf sseTaint τA (.block (clrTop VG.Impl.Rsa.X86.Recover.mY)))).isSome = true := by
  taint_decide

theorem clrTop_mXCheck : (VG.Taint.check sseTaint τA (.block (clrTop VG.Impl.Rsa.X86.Recover.mX)) (VG.Taint.hintOf sseTaint τA (.block (clrTop VG.Impl.Rsa.X86.Recover.mX)))).isSome = true := by
  taint_decide

theorem mulArgs_mXm_mXm_mR2Check : (VG.Taint.check sseTaint τF (.block (mulArgs VG.Impl.Rsa.X86.Recover.mXm VG.Impl.Rsa.X86.Recover.mXm VG.Impl.Rsa.X86.Recover.mR2)) (.block [])).isSome = true := by
  taint_decide

theorem mulArgs_mG_mG_mR2Check : (VG.Taint.check sseTaint τF (.block (mulArgs VG.Impl.Rsa.X86.Recover.mG VG.Impl.Rsa.X86.Recover.mG VG.Impl.Rsa.X86.Recover.mR2)) (.block [])).isSome = true := by
  taint_decide

theorem mulArgs_mXm_mXm_mGCheck : (VG.Taint.check sseTaint τF (.block (mulArgs VG.Impl.Rsa.X86.Recover.mXm VG.Impl.Rsa.X86.Recover.mXm VG.Impl.Rsa.X86.Recover.mG)) (.block [])).isSome = true := by
  taint_decide

theorem mulArgs_mY_mY_mYCheck : (VG.Taint.check sseTaint τF (.block (mulArgs VG.Impl.Rsa.X86.Recover.mY VG.Impl.Rsa.X86.Recover.mY VG.Impl.Rsa.X86.Recover.mY)) (.block [])).isSome = true := by
  taint_decide

theorem mulArgs_mY_mY_mXmCheck : (VG.Taint.check sseTaint τF (.block (mulArgs VG.Impl.Rsa.X86.Recover.mY VG.Impl.Rsa.X86.Recover.mY VG.Impl.Rsa.X86.Recover.mXm)) (.block [])).isSome = true := by
  taint_decide

theorem mulArgs_mX_mY_mYCheck : (VG.Taint.check sseTaint τF (.block (mulArgs VG.Impl.Rsa.X86.Recover.mX VG.Impl.Rsa.X86.Recover.mY VG.Impl.Rsa.X86.Recover.mY)) (.block [])).isSome = true := by
  taint_decide

end VG.Proof.Rsa.X86.Recover
