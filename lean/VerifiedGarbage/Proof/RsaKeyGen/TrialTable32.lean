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

theorem packed_length : packed.length = 1024 := by simp only [packed, List.length_map, List.length_range]

theorem packed_entry {i : Nat} (bound : i < 1024) :
    packed[i]'(by rw [packed_length]; exact bound) = BitVec.ofNat 64 (entry i) := by
  simp only [packed, List.getElem_map, List.getElem_range]

theorem entry_bound {i : Nat} (bound : i < 1024) : entry i < 2 ^ 64 := by
  have prime := (VG.Proof.RsaKeyGen.tabEntry_facts bound).2.2
  have inv := (inverse (BitVec.ofNat 32 (tabEntry i))).isLt
  unfold entry
  omega

theorem entry_low {i : Nat} (bound : i < 1024) : entry i % 2 ^ 32 = tabEntry i := by
  have prime := (VG.Proof.RsaKeyGen.tabEntry_facts bound).2.2
  unfold entry
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem entry_high {i : Nat} (bound : i < 1024) :
    entry i / 2 ^ 32 = (inverse (BitVec.ofNat 32 (tabEntry i))).toNat := by
  have prime := (VG.Proof.RsaKeyGen.tabEntry_facts bound).2.2
  unfold entry
  rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2 ^ 32), Nat.div_eq_of_lt (by omega), Nat.zero_add]

end VG.Proof.RsaKeyGen.TrialTable32
