module

public import VerifiedGarbage.Proof.Framework.Arm.CallerTransform
public import VerifiedGarbage.Proof.Framework.SubstLocal
public import VerifiedGarbage.Impl.Bignum.Arm.Row

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
