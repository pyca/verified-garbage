module

/-!
# Bit `j` of a byte, as code extracts it

Code that writes a byte's bits one by one widens the byte to a register of
`w ≥ 8` bits, shifts it right by `j`, masks it with `1` and stores the low
byte (`bitByte`): bit `j` of the byte (`bitByte_getLsbD`). Proven through
`toNat`, for every byte and position at once.
-/

@[expose] public section

namespace VG

theorem bitByte (w : Nat) (hw : 8 ≤ w) (b : BitVec 8) (j : Nat) :
    (((b.setWidth w >>> j) &&& 1).setWidth 8 : BitVec 8) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1) := by
  apply BitVec.eq_of_toNat_eq
  have h8 : 2 ^ 8 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
  have hb := b.isLt
  have h1 : (1 : BitVec w).toNat = 1 := by
    show (BitVec.ofNat w 1).toNat = 1; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ushiftRight, h1, BitVec.toNat_ofNat,
    Nat.and_one_is_mod]
  rw [Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ w)]

theorem ofNat_bit (b : BitVec 8) (j : Nat) :
    BitVec.ofNat 8 ((b.toNat >>> j) &&& 1) = if b.getLsbD j then 1 else 0 := by
  rw [Nat.and_one_is_mod, BitVec.getLsbD, Nat.testBit, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (b.toNat >>> j) with h | h <;> simp [h]

theorem bitByte_getLsbD (w : Nat) (hw : 8 ≤ w) (b : BitVec 8) (j : Nat) :
    (((b.setWidth w >>> j) &&& 1).setWidth 8 : BitVec 8) = if b.getLsbD j then 1 else 0 := by
  rw [bitByte w hw, ofNat_bit]

end VG
