module

public import VerifiedGarbage.Proof.Framework.Subst
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.TCB.Arm.Target

/-! Behavior-preserving implementation choices inherited by generic callers. -/

@[expose] public section
namespace VG.Arm
open VG

structure CallerTransform where
  code : Prog isa → Prog isa
  sim : ∀ c, Sim c (code c)
  stack_le : ∀ c, FrameStack.armStack (code c) ≤ FrameStack.armStack c
  calls_eq : ∀ c, (code c).calls = c.calls

def CallerTransform.identity : CallerTransform where
  code := id
  sim := by intro c s tr s' h; exact h
  stack_le := fun _ => Nat.le_refl _
  calls_eq := fun _ => rfl

/-- The same contract, including its constants and timing relation, is retained. -/
theorem CallerTransform.verified (f : CallerTransform) {c : Prog isa} {k : Contract isa}
    (h : Verified target c k) : Verified target (f.code c) k := h.of_sim (f.sim c)

end VG.Arm
