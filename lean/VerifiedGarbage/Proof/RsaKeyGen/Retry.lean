module

public import VerifiedGarbage.Spec.RsaKeyGen
import Mathlib.Data.Nat.Basic

/-! # The released retry status identifies exactly the small private inverse -/

@[expose] public section
namespace VG.Proof.RsaKeyGen
open VG

theorem keyFromPrimes_retry_iff (nlen e p q : Nat) :
    Spec.RsaKeyGen.keyFromPrimes nlen e p q = .inr () ↔
      ∃ d, Spec.Rsa.inverse e (Nat.lcm (max p q - 1) (min p q - 1)) = some d ∧ d ≤ 2 ^ (nlen / 2) := by
  have sorted : (if p < q then (q, p) else (p, q)) = (max p q, min p q) := by
    by_cases order : p < q
    · simp only [order, ite_true, Nat.max_eq_right (Nat.le_of_lt order), Nat.min_eq_left (Nat.le_of_lt order)]
    · simp only [order, ite_false, Nat.max_eq_left (by omega : q ≤ p), Nat.min_eq_right (by omega : q ≤ p)]
  unfold Spec.RsaKeyGen.keyFromPrimes
  rw [sorted]
  dsimp only
  cases inv : Spec.Rsa.inverse e (Nat.lcm (max p q - 1) (min p q - 1)) with
  | none => simp
  | some d =>
    dsimp only
    by_cases small : d ≤ 2 ^ (nlen / 2)
    · simp [small]
    · rw [ite_eq_right small]
      cases other : Spec.Rsa.inverse (min p q) (max p q) with
      | none => simp [small]
      | some qi =>
        dsimp only
        split <;> simp [small]

end VG.Proof.RsaKeyGen
