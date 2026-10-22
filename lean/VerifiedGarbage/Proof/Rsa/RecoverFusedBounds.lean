module

public import VerifiedGarbage.Proof.Rsa.RecoverFused
import Mathlib.Data.Nat.Basic

/-! Bounds for the saved root, including failed and invalid-key searches. -/

@[expose] public section
namespace VG.Proof.Rsa.Fused

def Bounded (n : Nat) (s : State) : Prop :=
  s.value < n ∧ ∀ y, s.root = some y → y < n

theorem bounded_start {n y : Nat} (hy : y < n) : Bounded n (start n y) :=
  ⟨hy, by intro r h; cases h⟩

theorem bounded_step {n b : Nat} {bit : Bool} {s : State}
    (hn : 0 < n) (h : Bounded n s) : Bounded n (step n b bit s) := by
  refine ⟨step_lt n b bit s hn, ?_⟩
  intro y root
  rw [step_root] at root
  cases bit
  · simp only [Bool.false_eq_true, ↓reduceIte] at root
    split at root
    · cases root; exact h.1
    · exact h.2 y root
  · cases root

theorem bounded_bits {n b k e : Nat} {s : State}
    (hn : 0 < n) (h : Bounded n s) : Bounded n (bits n b k e s) := by
  induction k generalizing s with
  | zero => exact h
  | succ k ih => exact ih (bounded_step hn h)

theorem bounded_eval {n b e : Nat} (hn : 1 < n) : Bounded n (eval n b e) := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    rw [eval]
    split
    · exact bounded_start hn
    · exact bounded_step (by omega) (ih (e / 2) (by omega))

theorem root_getD_lt {n : Nat} {s : State} (hn : 0 < n) (h : Bounded n s) :
    s.root.getD 0 < n := by
  cases hr : s.root with
  | none => exact hn
  | some y => exact h.2 y hr

end VG.Proof.Rsa.Fused
