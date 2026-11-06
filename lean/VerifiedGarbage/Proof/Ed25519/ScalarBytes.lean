module
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Ed25519.Contract

import VerifiedGarbage.Proof.Ed25519.Bytes

/-!
# The bytes of a little-endian scalar are its base-256 digits, its nibbles its base-16 ones

Apart from the group facts of windowed multiplication (`Window.lean`), so that code
reading a scalar's bytes need not import the group's algebra.
-/

@[expose] public section

namespace VG.Proof.Ed25519

theorem decodeLE_byte : ∀ (bs : List Byte) (i : Nat),
    Spec.Ed25519.decodeLE bs / 256 ^ i % 256 = (bs.getD i 0).toNat
  | [], i => by simp [Spec.Ed25519.decodeLE]
  | b :: bs, 0 => by
    simp only [Spec.Ed25519.decodeLE, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]
    have := b.isLt; omega
  | b :: bs, i + 1 => by
    rw [List.getD_cons_succ, ← decodeLE_byte bs i, Spec.Ed25519.decodeLE, Nat.pow_succ,
      Nat.mul_comm (256 ^ i), ← Nat.div_div_eq_div_mul]
    congr 2
    have := b.isLt; omega

theorem div_split (x i : Nat) : x / 256 ^ i = 256 * (x / 256 ^ (i + 1)) + x / 256 ^ i % 256 := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]; omega

theorem high_zero {S i : Nat} (hS : S < 256 ^ 32) (hi : 32 ≤ i) : S / 256 ^ i = 0 :=
  Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hS (Nat.pow_le_pow_right (by decide) hi))

theorem decodeLE_lt32 (m : Mem) (p : Addr) :
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32) < 256 ^ 32 := by
  have h := decodeLE_lt (Spec.Ed25519.bytesAt m p 32)
  rwa [show (Spec.Ed25519.bytesAt m p 32).length = 32 by simp [Spec.Ed25519.bytesAt]] at h

theorem decodeLE_lt64 (m : Mem) (p : Addr) :
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 64) < 256 ^ 64 := by
  have h := decodeLE_lt (Spec.Ed25519.bytesAt m p 64)
  rwa [show (Spec.Ed25519.bytesAt m p 64).length = 64 by simp [Spec.Ed25519.bytesAt]] at h

/-! ## Nibbles: two base-16 digits per byte -/

/-- Nibble `i` of the bytes `bs`: the high nibble of byte `i / 2` if `i` is odd, its low nibble
if `i` is even. -/
def nibbleOf (bs : List Byte) (i : Nat) : Nat :=
  if i % 2 = 1 then (bs.getD (i / 2) 0).toNat / 16 else (bs.getD (i / 2) 0).toNat % 16

theorem nibbleOf_lt (bs : List Byte) (i : Nat) : nibbleOf bs i < 16 := by
  have := (bs.getD (i / 2) 0).isLt
  unfold nibbleOf; split <;> omega

theorem pow16_eq (i : Nat) : 16 ^ i = 256 ^ (i / 2) * 16 ^ (i % 2) := by
  calc 16 ^ i = 16 ^ (2 * (i / 2) + i % 2) := by rw [Nat.div_add_mod]
    _ = 256 ^ (i / 2) * 16 ^ (i % 2) := by rw [Nat.pow_add, Nat.pow_mul]

theorem decodeLE_nibble (bs : List Byte) (i : Nat) :
    Spec.Ed25519.decodeLE bs / 16 ^ i % 16 = nibbleOf bs i := by
  have hb := decodeLE_byte bs (i / 2)
  rw [pow16_eq, ← Nat.div_div_eq_div_mul]
  unfold nibbleOf
  generalize Spec.Ed25519.decodeLE bs / 256 ^ (i / 2) = y at hb
  generalize (bs.getD (i / 2) 0).toNat = b at hb
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [h, ite_eq_right (by decide), Nat.pow_zero, Nat.div_one]; omega
  · rw [h, ite_eq_left rfl, Nat.pow_one]; omega

theorem nibble_split (x i : Nat) : x / 16 ^ i = 16 * (x / 16 ^ (i + 1)) + x / 16 ^ i % 16 := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]; omega

/-- Two nibbles per byte. -/
theorem div_pow16_two_mul (x c : Nat) : x / 16 ^ (2 * c) = x / 256 ^ c := by
  rw [Nat.pow_mul]

/-- A scalar below `256^32` has no nibble from 64 up. -/
theorem nibble_high_zero {S i : Nat} (hS : S < 256 ^ 32) (hi : 64 ≤ i) : S / 16 ^ i = 0 :=
  Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (by rwa [show (256 : Nat) ^ 32 = 16 ^ 64 from rfl] at hS)
    (Nat.pow_le_pow_right (by decide) hi))

end VG.Proof.Ed25519
