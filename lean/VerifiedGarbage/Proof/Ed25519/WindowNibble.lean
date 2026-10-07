import VerifiedGarbage.Proof.Ed25519.Window

/-!
# Verification with windows, nibble by nibble

Target-independent facts for windows taken one nibble at a time: nibble `i`
of a little-endian scalar is its base-16 digit `i`, read from byte `i / 2`
(`decodeLE_nibble`), and a window takes the sum of the nibbles from `i + 1`
up to that from `i` (`nibble_step`).
-/

namespace VG.Proof.Ed25519

open Edwards

/-- Nibble `i` of the bytes `bs`: the high nibble of byte `i / 2` if `i` is odd, its low nibble
if `i` is even. -/
def nibbleOf (bs : List Byte) (i : Nat) : Nat :=
  if i % 2 = 1 then (bs.getD (i / 2) 0).toNat / 16 else (bs.getD (i / 2) 0).toNat % 16

theorem nibbleOf_lt (bs : List Byte) (i : Nat) : nibbleOf bs i < 16 := by
  have := (bs.getD (i / 2) 0).isLt
  unfold nibbleOf; split <;> omega

theorem pow16_eq (i : Nat) : 16 ^ i = 256 ^ (i / 2) * 16 ^ (i % 2) := by
  conv_lhs => rw [← Nat.div_add_mod i 2, pow_add, pow_mul]
  rfl

theorem decodeLE_nibble (bs : List Byte) (i : Nat) :
    Spec.Ed25519.decodeLE bs / 16 ^ i % 16 = nibbleOf bs i := by
  have hb := decodeLE_byte bs (i / 2)
  rw [pow16_eq, ← Nat.div_div_eq_div_mul]
  unfold nibbleOf
  generalize Spec.Ed25519.decodeLE bs / 256 ^ (i / 2) = y at hb
  generalize (bs.getD (i / 2) 0).toNat = b at hb
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [h, ite_eq_right (by decide), pow_zero, Nat.div_one]; omega
  · rw [h, ite_eq_left rfl, pow_one]; omega

theorem nibble_split (x i : Nat) : x / 16 ^ i = 16 * (x / 16 ^ (i + 1)) + x / 16 ^ i % 16 := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul]; omega

/-- The windows' sum, one nibble on: `16` times the sum so far plus the digits. -/
theorem nibble_step (A N : EPoint dZ) (K S i : Nat) :
    (16 : Nat) • ((K / 16 ^ (i + 1)) • A + (S / 16 ^ (i + 1)) • N) + (K / 16 ^ i % 16) • A +
      (S / 16 ^ i % 16) • N = (K / 16 ^ i) • A + (S / 16 ^ i) • N := by
  have hK := nibble_split K i
  have hS := nibble_split S i
  generalize K / 16 ^ i % 16 = kr at hK ⊢
  generalize S / 16 ^ i % 16 = sr at hS ⊢
  rw [hK, hS]
  module

/-- Two nibbles per byte. -/
theorem div_pow16_two_mul (x c : Nat) : x / 16 ^ (2 * c) = x / 256 ^ c := by
  rw [pow_mul]; rfl

/-- A scalar below `256^32` has no nibble from 64 up. -/
theorem nibble_high_zero {S i : Nat} (hS : S < 256 ^ 32) (hi : 64 ≤ i) : S / 16 ^ i = 0 :=
  Nat.div_eq_of_lt (lt_of_lt_of_le (by rwa [show (256 : Nat) ^ 32 = 16 ^ 64 from rfl] at hS)
    (Nat.pow_le_pow_right (by decide) hi))

end VG.Proof.Ed25519
