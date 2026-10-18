module

public import VerifiedGarbage.Proof.Mont.Words32

/-! # Bit arithmetic for 32-bit RSA key workspaces -/

@[expose] public section
namespace VG.Proof.Rsa.KeyBits32
theorem or_one (n : Nat) : n ||| 1 = 2 * (n / 2) + 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  rcases i with _ | i
  · simp [Nat.testBit_zero]
  · rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
      show (2 * (n / 2) + 1) / 2 = n / 2 by omega]
    simp

theorem xor_one (n : Nat) : (2 * n + 1) ^^^ 1 = 2 * n := by
  apply Nat.eq_of_testBit_eq; intro i
  rcases i with _ | i
  · simp [Nat.testBit_zero]
  · rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
      show (2 * n + 1) / 2 = n by omega, show 2 * n / 2 = n by omega]
    simp

theorem bv_or_one (x : BitVec 32) : (x ||| (1 : BitVec 32)).toNat = 2 * (x.toNat / 2) + 1 := by
  rw [BitVec.toNat_or]; simp [or_one]

theorem bv_clr_one (x : BitVec 32) : ((x ||| (1 : BitVec 32)) ^^^ (1 : BitVec 32)).toNat = 2 * (x.toNat / 2) := by
  rw [BitVec.toNat_xor, BitVec.toNat_or]; simp [or_one, xor_one]

theorem bv_and_one (x : BitVec 32) : (x &&& (1 : BitVec 32)).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and]; simp [Nat.and_one_is_mod]

theorem bit_cases {x : BitVec 32} (h : x.toNat ≤ 1) : x = 0#32 ∨ x = (1 : BitVec 32) := by
  rcases (by omega : x.toNat = 0 ∨ x.toNat = 1) with e | e
  · exact .inl (BitVec.eq_of_toNat_eq (by simp [e]))
  · exact .inr (BitVec.eq_of_toNat_eq (by simp [e]))

theorem bv_and_bits {x y : BitVec 32} (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) :
    (x &&& y).toNat = if x.toNat = 1 ∧ y.toNat = 1 then 1 else 0 := by
  rcases bit_cases hx with rfl | rfl <;> rcases bit_cases hy with rfl | rfl <;> decide

theorem bv_xor_bits {x y : BitVec 32} (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) :
    (x ^^^ y).toNat = (x.toNat + y.toNat) % 2 := by
  rcases bit_cases hx with rfl | rfl <;> rcases bit_cases hy with rfl | rfl <;> decide

theorem bv_nor_bits {x y : BitVec 32} (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) :
    ((x ||| y) ^^^ (1 : BitVec 32)).toNat = if x.toNat = 0 ∧ y.toNat = 0 then 1 else 0 := by
  rcases bit_cases hx with rfl | rfl <;> rcases bit_cases hy with rfl | rfl <;> decide

end VG.Proof.Rsa.KeyBits32
