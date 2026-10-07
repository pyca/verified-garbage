import VerifiedGarbage.Proof.Rsa.RecoverMath

/-!
# `recoverPrimes`: the number of tries

The candidates tried, `(recoverPrimes.go n t r recoverTries).2`, are at
most `recoverTries` (`go_le`), and the candidate loop stops after
candidate `j` iff `j + 1` is that number (`cand_cond`): which the
implementations' constant-time proofs need, as the number of tries is
public.
-/

namespace VG.Proof.Rsa

open VG.Spec.Rsa (splitTwos recoverStep recoverPrimes recoverTries)

/-! ## The number of tries -/

theorem go_ge (n t r : Nat) : ∀ k, k ≤ recoverTries → recoverTries - k ≤ (recoverPrimes.go n t r k).2
  | 0, _ => by rw [recoverPrimes.go]; exact Nat.le_refl _
  | k + 1, hk => by
    rw [recoverPrimes.go]
    split
    · show recoverTries - (k + 1) ≤ recoverTries - k
      omega
    · have := go_ge n t r k (by omega)
      omega

theorem go_le (n t r : Nat) : ∀ k, k ≤ recoverTries → (recoverPrimes.go n t r k).2 ≤ recoverTries
  | 0, _ => by rw [recoverPrimes.go]
  | k + 1, hk => by
    rw [recoverPrimes.go]
    split
    · show recoverTries - k ≤ recoverTries
      omega
    · exact go_le n t r k (by omega)

/-- After candidate `j` fails, at least `j + 2` are tried. -/
theorem go_ge1 (n t r : Nat) {k : Nat} (hk : k < recoverTries) :
    recoverTries - k ≤ (recoverPrimes.go n t r (k + 1)).2 := by
  rw [recoverPrimes.go]
  split
  · exact Nat.le_refl _
  · exact go_ge n t r k (by omega)

/-- The loop's condition after candidate `j`, from the tries. -/
theorem cand_cond (n t r : Nat) {j : Nat} (hj : j < (recoverPrimes.go n t r recoverTries).2)
    (hgo : recoverPrimes.go n t r recoverTries = recoverPrimes.go n t r (recoverTries - j)) :
    (!(!(decide (j + 1 < 100) && !(recoverStep n t r (j + 2)).isSome))) =
      decide (j + 1 < (recoverPrimes.go n t r recoverTries).2) := by
  have hle := go_le n t r recoverTries (Nat.le_refl _)
  have hj100 : j < recoverTries := by omega
  rw [hgo, go_eq n t r hj100]
  cases hs : recoverStep n t r (j + 2) with
  | some y => simp
  | none =>
    simp only [Option.isSome_none, Bool.not_false, Bool.and_true, Bool.not_not]
    by_cases h1 : j + 1 < 100
    · obtain ⟨k, hk⟩ : ∃ k, recoverTries - (j + 1) = k + 1 := ⟨recoverTries - (j + 1) - 1, by unfold recoverTries; omega⟩
      have := go_ge1 n t r (k := k) (by unfold recoverTries at *; omega)
      rw [hk]
      simp only [h1, decide_true]
      exact (decide_eq_true (by unfold recoverTries at *; omega)).symm
    · have e : recoverTries - (j + 1) = 0 := by unfold recoverTries; omega
      rw [e, recoverPrimes.go]
      simp only [h1, decide_false]
      exact (decide_eq_false (by unfold recoverTries; omega)).symm

end VG.Proof.Rsa
