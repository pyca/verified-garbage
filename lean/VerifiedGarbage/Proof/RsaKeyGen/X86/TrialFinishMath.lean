module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialWord

/-! # Convert the bounded Montgomery residue into a divisibility bit -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Trial
open VG

theorem word_zero (x : BitVec 32) : decide (x.toNat < (1 : BitVec 32).toNat) = decide (x = 0#32) := by
  apply decide_eq_decide.mpr
  rw [← BitVec.toNat_inj]
  change x.toNat < 1 ↔ x.toNat = 0
  omega

theorem sub_zero (a b : BitVec 32) : a - b = 0#32 ↔ a = b := by
  rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add]

theorem finish_bits (a b : BitVec 32) (positive : 0 < b.toNat) :
    ((0#32 + 0 + carryWord (decide (a.toNat < (1 : BitVec 32).toNat))) + 0 +
      carryWord (decide ((a - b).toNat < (1 : BitVec 32).toNat))) =
      BitVec.ofNat 32 (decide (a.toNat = 0 ∨ a.toNat = b.toNat)).toNat := by
  rw [word_zero, word_zero]
  have zeroIff : a.toNat = 0 ↔ a = 0#32 := by rw [← BitVec.toNat_inj]; rfl
  have eqIff : a.toNat = b.toNat ↔ a = b := BitVec.toNat_inj
  simp only [sub_zero, zeroIff, eqIff]
  by_cases zero : a = 0#32
  · have different : a ≠ b := by intro eq; rw [← eq, zero] at positive; contradiction
    rw [decide_eq_true zero, decide_eq_false different, decide_eq_true (Or.inl zero)]
    rfl
  · by_cases same : a = b
    · rw [decide_eq_false zero, decide_eq_true same, decide_eq_true (Or.inr same)]
      rfl
    · rw [decide_eq_false zero, decide_eq_false same, decide_eq_false (not_or_intro zero same)]
      rfl

end VG.Proof.RsaKeyGen.X86.Trial
