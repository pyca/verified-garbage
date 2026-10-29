module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyReady

import VerifiedGarbage.Spec.RsaKeyGen
import Mathlib.Data.Nat.Basic
/-! # The secret native retry comparison equals the released shared result -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/Retry.lean`, which only this module imported.
section

/-! # The released retry status identifies exactly the small private inverse -/

section
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
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem KeyReady.retry_iff {B : Addr} {n e p q : Nat} {m : Mem} (R : KeyReady B n e p q m) :
    (slot m B kOk = 1 ∧ num m B n aD ≤ 2 ^ (16 * n)) ↔
      Spec.RsaKeyGen.keyFromPrimes (32 * n) e p q = .inr () := by
  rw [VG.Proof.RsaKeyGen.keyFromPrimes_retry_iff, show 32 * n / 2 = 16 * n by omega, R.inverse]
  by_cases zero : slot m B kOk = 0
  · simp only [zero, ite_true, reduceCtorEq, false_and, exists_false]
  · have one : slot m B kOk = 1 := by have := R.bit; omega
    simp [one]

end VG.Proof.RsaKeyGen.X86.Key
