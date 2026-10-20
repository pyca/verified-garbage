module

public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # Certify the prepared inverse of every sieve divisor -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.TrialTable32
open VG VG.Impl.RsaKeyGen
open VG.Impl.RsaKeyGen.TrialTable32

/-- Evaluation is over the shared, proved small-prime table, not an untrusted
list of divisors supplied to the implementation. -/
theorem inverses_valid : slots.all (fun s =>
    (s * (inverse (BitVec.ofNat 32 s)).toNat + 1) % 2 ^ 32 == 0) = true := by
  unfold slots
  rw [primes.lit_eq]
  decide +kernel

theorem inverse_entry {i : Nat} (bound : i < 1024) :
    (tabEntry i * (inverse (BitVec.ofNat 32 (tabEntry i))).toNat + 1) % 2 ^ 32 = 0 := by
  have valid := List.all_eq_true.mp inverses_valid (slots[i]'(by rw [slots_length]; exact bound))
    (List.getElem_mem _)
  simp only [beq_iff_eq] at valid
  have slot : tabEntry i = slots[i]'(by rw [slots_length]; exact bound) := by
    unfold tabEntry
    exact getD_of_lt _
  rw [slot]
  exact valid

end VG.Proof.RsaKeyGen.TrialTable32
