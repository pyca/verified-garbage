import VerifiedGarbage.Proof.Ed25519.Bytes

/-!
# The bytes of a little-endian scalar are its base-256 digits

Apart from the group facts of windowed multiplication (`Window.lean`), so that code
reading a scalar's bytes need not import the group's algebra.
-/

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

theorem byte_split (K i : Nat) (b : Byte) (hb : (b.toNat) = K / 256 ^ i % 256) :
    K / 256 ^ i = 256 * (K / 256 ^ (i + 1)) + (16 * (b.toNat / 16) + b.toNat % 16) := by
  have := div_split K i; omega

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

end VG.Proof.Ed25519
