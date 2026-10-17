module

public import VerifiedGarbage.Spec.Ffdh

@[expose] public section

namespace VG.Proof.Ffdh
open VG

/-- The mask expression really selects by the low bit, for all words. -/
theorem choose_low_bit (a b bit : BitVec 64) :
    Spec.Ffdh.choose a b bit = if bit &&& 1 = 0 then a else b := by
  unfold Spec.Ffdh.choose
  have hl : (bit &&& 1).toNat ≤ 1 := by
    simp only [BitVec.toNat_and]
    exact Nat.and_le_right
  by_cases h : bit &&& 1 = 0
  · rw [h]
    simp only [BitVec.sub_self, BitVec.and_zero, BitVec.xor_zero, ↓reduceIte]
  · have h1 : bit &&& 1 = 1 := by
      apply BitVec.eq_of_toNat_eq
      have hn : (bit &&& 1).toNat ≠ 0 := by
        intro hz
        exact h (BitVec.eq_of_toNat_eq hz)
      change (bit &&& 1).toNat = 1
      omega
    rw [ite_eq_right h, h1]
    change a ^^^ ((a ^^^ b) &&& BitVec.allOnes 64) = b
    rw [BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
end VG.Proof.Ffdh
