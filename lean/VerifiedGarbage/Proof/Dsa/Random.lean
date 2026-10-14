module

public import VerifiedGarbage.Spec.Dsa.Random
import VerifiedGarbage.Proof.Framework.Omega

/-! # Scalar-sampling invariants shared by randomized signing and key generation

These establish the bounds needed by the byte-tape implementation without
assuming primality, supported domain sizes, or uniformly distributed inputs.
-/

@[expose] public section

namespace VG.Proof.Dsa.Random
open VG.Spec.Dsa.Random

/-- Every successful sample is a nonzero scalar strictly below q. -/
theorem sample_range (q fuel : Nat) (rand : List VG.Byte) (k : Nat)
    (hk : (sample q fuel rand).scalar = some k) : 0 < k ∧ k < q := by
  induction fuel generalizing rand with
  | zero => simp [sample] at hk
  | succ fuel ih =>
    simp only [sample] at hk
    split at hk
    · simp at hk
    · split at hk
      · simp at hk
      · split at hk
        next h =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          cases hk
          exact h
        next _ => exact ih _ hk

/-- The sampler never consumes a partial draw or reads beyond its tape. -/
theorem sample_used_le (q fuel : Nat) (rand : List VG.Byte) :
    (sample q fuel rand).used ≤ rand.length := by
  induction fuel generalizing rand with
  | zero => simp [sample]
  | succ fuel ih =>
    simp only [sample]
    split
    · simp
    · split
      · simp
      next h =>
        split
        · simp only
          omega
        · have hi := ih (rand.drop (drawBytes q))
          simp only [List.length_drop] at hi
          simp only
          omega

/-- At most one fixed-width chunk is consumed per draw. -/
theorem sample_used_budget (q fuel : Nat) (rand : List VG.Byte) :
    (sample q fuel rand).used ≤ fuel * drawBytes q := by
  induction fuel generalizing rand with
  | zero => simp [sample]
  | succ fuel ih =>
    simp only [sample]
    split
    · simp
    · split
      · simp
      · split
        · simp only
          rw [Nat.succ_mul]
          omega
        · have hi := ih (rand.drop (drawBytes q))
          simp only
          rw [Nat.succ_mul]
          omega

/-- Consumption is always a whole number of draws, even on failure. -/
theorem sample_used_multiple (q fuel : Nat) (rand : List VG.Byte) :
    drawBytes q ∣ (sample q fuel rand).used := by
  induction fuel generalizing rand with
  | zero => simp [sample]
  | succ fuel ih =>
    simp only [sample]
    split
    · simp
    · split
      · simp
      · split
        · exact Nat.dvd_refl _
        · exact Nat.dvd_add (Nat.dvd_refl _) (ih _)

/-- The public trace accounts for every consumed draw. Neither the accepted
scalar nor the contents of rejected draws are needed to recover consumption. -/
theorem sample_used_trace (q fuel : Nat) (rand : List VG.Byte) :
    (sample q fuel rand).used = drawBytes q *
      ((sample q fuel rand).trace.count 0 + (sample q fuel rand).trace.count 1) := by
  induction fuel generalizing rand with
  | zero => simp [sample]
  | succ fuel ih =>
    simp only [sample]
    split
    · simp
    · split
      · simp
      · split
        · simp
        · simp only [List.count_cons, beq_self_eq_true, Nat.reduceBEq,
            ite_true, Bool.false_eq_true, ite_false, Nat.add_zero]
          rw [ih]
          simp only [Nat.add_right_comm _ 1, Nat.mul_add, Nat.mul_one]
          exact Nat.add_comm _ _

/-- Equal public sampling traces imply equal byte consumption. -/
theorem sample_used_eq_of_trace_eq (q fuel₁ fuel₂ : Nat) (rand₁ rand₂ : List VG.Byte)
    (h : (sample q fuel₁ rand₁).trace = (sample q fuel₂ rand₂).trace) :
    (sample q fuel₁ rand₁).used = (sample q fuel₂ rand₂).used := by
  rw [sample_used_trace, sample_used_trace, h]

end VG.Proof.Dsa.Random
