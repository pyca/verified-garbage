module

import VerifiedGarbage.Proof.Bignum.Arm.MontMath
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Packed-word Montgomery coefficients, capacity bounds, and exact division -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Proof.Mont

theorem val32_mod_low (mem : Mem) (base : Addr) (acc n : Nat) :
    val32 mem base acc (n + 1) % 2 ^ 32 = w32 mem base acc := by
  rw [val32, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (mem.readW (off base acc) 32).isLt]

theorem coefficient_value (inv : BitVec 32) (mem : Mem) (base : Addr) (acc n : Nat) :
    (inv * mem.readW (off base acc) 32).toNat =
      (val32 mem base acc (n + 1) * inv.toNat) % 2 ^ 32 := by
  rw [BitVec.toNat_mul, Nat.mul_mod (val32 mem base acc (n + 1)) inv.toNat,
    val32_mod_low, Nat.mod_eq_of_lt inv.isLt]
  exact congrArg (fun x => x % 2 ^ 32) (Nat.mul_comm _ _)

/-- Both additions fit in the accumulator's two extension words. -/
theorem round_fit {T a b u m n : Nat} (hT : T < 2 * m) (ha : a < 2 ^ 32)
    (hb : b < m) (hu : u < 2 ^ 32) (hm : m < 2 ^ (32 * n)) :
    T + a * b + u * m < 2 ^ (32 * (n + 2)) := by
  have sum := round_sum_lt hT ha hb hu
  rw [Nat.mul_add, Nat.pow_add]
  change T + a * b + u * m < 2 ^ (32 * n) * 2 ^ 64
  omega

theorem round_cancel {T T' u m inv : Nat} (hi : (m * inv + 1) % 2 ^ 32 = 0)
    (hu : u = T * inv % 2 ^ 32) (hs : T' = T + u * m) : T' % 2 ^ 32 = 0 := by
  rw [hs, hu, Nat.add_comm]
  exact mont_low T inv m hi

/-- Cancellation makes the right shift an exact division by the limb radix. -/
theorem round_div_exact {T : Nat} (h : T % 2 ^ 32 = 0) : 2 ^ 32 * (T / 2 ^ 32) = T := by
  have eq := Nat.mod_add_div T (2 ^ 32)
  simpa only [h, Nat.zero_add] using eq

end VG.Proof.Bignum.Arm
