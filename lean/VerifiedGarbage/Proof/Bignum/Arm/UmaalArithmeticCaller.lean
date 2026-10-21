module

import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmetic
public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaalCaller
public import VerifiedGarbage.Proof.Bignum.Arm.DownRowUmaal
import VerifiedGarbage.Impl.Bignum.Arm.DownRow

/-! Generic callers inherit both row choices without changing named calls. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem armStack_downLocal (c : Prog isa) :
    FrameStack.armStack (Code.substLocal DownRow.code DownRow.codeU c) ≤ FrameStack.armStack c := by
  induction c with
  | block _ => simp only [Code.substLocal]; split <;> simp [DownRowUmaal.codeU_stack, FrameStack.armStack]
  | seq a b iha ihb =>
    simp only [Code.substLocal]; split
    · simp [DownRowUmaal.codeU_stack]
    · simp only [FrameStack.armStack]; omega
  | ite _ t e iht ihe =>
    simp only [Code.substLocal]; split
    · simp [DownRowUmaal.codeU_stack]
    · simp only [FrameStack.armStack]; omega
  | loop b _ ih =>
    simp only [Code.substLocal]; split
    · simp [DownRowUmaal.codeU_stack]
    · simpa only [FrameStack.armStack] using ih
  | call _ _ _ => exact Nat.le_refl _
  | frame i _ _ ih =>
    simp only [Code.substLocal]; split
    · simp [DownRowUmaal.codeU_stack]
    · cases i <;> simp only [FrameStack.armStack] <;> omega

def downCaller : CallerTransform where
  code := Code.substLocal DownRow.code DownRow.codeU
  sim := by intro c s tr t h;exact Exec.substLocal DownRowUmaal.code_sim h
  stack_le := armStack_downLocal
  calls_eq := fun c => Code.calls_substLocal (M := isa)
    (a := DownRow.code) (b := DownRow.codeU) (c := c) (by rfl) (by rfl)

def umaalArithmeticCaller : CallerTransform where
  code := fun c => downCaller.code (umaalCaller.code c)
  sim := by intro c s tr t h;exact downCaller.sim _ (umaalCaller.sim c h)
  stack_le := fun c => Nat.le_trans (downCaller.stack_le _) (umaalCaller.stack_le c)
  calls_eq := fun c => (downCaller.calls_eq _).trans (umaalCaller.calls_eq c)

end VG.Proof.Bignum.Arm
