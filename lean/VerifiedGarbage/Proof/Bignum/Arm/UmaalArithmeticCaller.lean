module

public import VerifiedGarbage.Proof.Bignum.Arm.DownRowUmaal
public import VerifiedGarbage.Proof.Framework.Arm.CallerTransform
public import VerifiedGarbage.Proof.Framework.SubstLocal
public import VerifiedGarbage.Impl.Bignum.Arm.Row
public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal

import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmetic
import VerifiedGarbage.Impl.Bignum.Arm.DownRow
/-! Generic callers inherit both row choices without changing named calls. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/RowCaller.lean`, which only this module imported.
section

/-! A row implementation can optimize inline caller arithmetic without touching calls. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem armStack_rowLocal (replacement : Prog isa)
    (stack : FrameStack.armStack replacement = 0) (c : Prog isa) :
    FrameStack.armStack (Code.substLocal row replacement c) ≤ FrameStack.armStack c := by
  induction c with
  | block _ => simp only [Code.substLocal]; split <;> simp [FrameStack.armStack, stack]
  | seq a b iha ihb =>
    simp only [Code.substLocal]; split
    · simp [stack]
    · simp only [FrameStack.armStack]; omega
  | ite _ t e iht ihe =>
    simp only [Code.substLocal]; split
    · simp [stack]
    · simp only [FrameStack.armStack]; omega
  | loop b _ ih =>
    simp only [Code.substLocal]; split
    · simp [stack]
    · simpa only [FrameStack.armStack] using ih
  | call _ _ _ => exact Nat.le_refl _
  | icall => exact Nat.le_refl _
  | frame i _ _ ih =>
    simp only [Code.substLocal]; split
    · simp [stack]
    · cases i <;> simp only [FrameStack.armStack] <;> omega

/-- Any verified call-free, frame-free row replacement supplies a caller decorator. -/
def rowCaller (replacement : Prog isa) (sim : Sim row replacement)
    (stack : FrameStack.armStack replacement = 0) (calls : replacement.calls = []) : CallerTransform where
  code := Code.substLocal row replacement
  sim := by intro c s tr s' h; exact Exec.substLocal sim h
  stack_le := armStack_rowLocal replacement stack
  calls_eq := fun _ => Code.calls_substLocal (by rfl) calls

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/RowUmaalCaller.lean`, which only this module imported.
section

/-! UMAAL arithmetic inherited by callers of the shared Montgomery backend. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG.Impl.Bignum.Arm

def umaalCaller : VG.Arm.CallerTransform := rowCaller rowU row_sim rfl rfl

end VG.Proof.Bignum.Arm
end

end

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
  | icall => exact Nat.le_refl _
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
