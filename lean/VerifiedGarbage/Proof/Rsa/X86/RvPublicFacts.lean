module
public import VerifiedGarbage.Proof.Rsa.X86.RvResult

import VerifiedGarbage.Proof.Rsa.RecoverTries

/-! # The refusal branch is determined by the declared recovery attempt count -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86
open VG.Impl.Rsa.X86.Recover
open VG.Spec.Rsa (recoverPrimes)

theorem recover_tries_positive (n e d : Nat) :
    0 < (recoverPrimes n e d).2 ↔ ¬(d * e < 2 ∨ (d * e - 1) % 2 = 1) := by
  by_cases h : d * e < 2 ∨ (d * e - 1) % 2 = 1
  · rw [VG.Proof.Rsa.recoverPrimes_none h]
    simp only [Nat.lt_irrefl, h, not_true]
  · rw [VG.Proof.Rsa.recoverPrimes_go h]
    have low := VG.Proof.Rsa.go_ge1 n (Spec.Rsa.splitTwos (d * e - 1)).1
      (Spec.Rsa.splitTwos (d * e - 1)).2 (k := 99) (by decide)
    change 1 ≤ (recoverPrimes.go n (Spec.Rsa.splitTwos (d * e - 1)).1
      (Spec.Rsa.splitTwos (d * e - 1)).2 100).2 at low
    exact ⟨fun _ => h, fun _ => low⟩

theorem calculated_tries_valid {g : CallGeometry} {m : Mem}
    (valid : Spec.Rsa.modulusValid (inputValue g m 0) (inputBytes g m 0).length = true) :
    (calculated g m).2 = (recoverPrimes (inputValue g m 0) (inputValue g m 1) (inputValue g m 2)).2 := by
  unfold calculated Spec.Rsa.primesKey
  dsimp only
  rw [show Spec.Rsa.modulusValid (Spec.Rsa.os2ip (inputBytes g m 0))
    (inputBytes g m 0).length = true from valid]
  simp only [ite_true]
  unfold inputValue
  generalize recoverPrimes (Spec.Rsa.os2ip (inputBytes g m 0)) (Spec.Rsa.os2ip (inputBytes g m 1))
    (Spec.Rsa.os2ip (inputBytes g m 2)) = result
  obtain ⟨opt, tries⟩ := result
  cases opt with
  | none => rfl
  | some pair => obtain ⟨p, q⟩ := pair; rfl

theorem Inputs.modulusFacts {g : CallGeometry} {s : State} (h : Inputs g s)
    (valid : Spec.Rsa.modulusValid (inputValue g s.mem 0) (inputBytes g s.mem 0).length = true) :
    inputValue g s.mem 0 < 2 ^ (64 * g.n) ∧ inputValue g s.mem 0 % 2 = 1 ∧
      101 < inputValue g s.mem 0 := by
  refine ⟨?_, ?_, ?_⟩
  · apply Nat.lt_of_lt_of_le (inputValue_lt g s.mem 0)
    apply Nat.pow_le_pow_right (by decide)
    have := h.inputBound 0
    omega
  all_goals simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at valid
  · exact valid.1.1.1
  · have lower := valid.1.1.2
    have power (k : Nat) (hk : 7 ≤ k) : 128 ≤ 2 ^ k := Nat.pow_le_pow_right (n := 2) (by decide) hk
    have bigger := power 511 (by decide)
    omega

end VG.Proof.Rsa.X86.Recover
