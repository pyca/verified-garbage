module
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp


/-! # Combining the low product and two cross products -/

@[expose] public section

namespace VG.Proof.Bignum.Arm

theorem mul64_value (a ah b bh lo hi : BitVec 32)
    (product : lo.toNat + hi.toNat * 2 ^ 32 = a.toNat * b.toNat) :
    ((hi + a * bh + b * ah) ++ lo) = (ah ++ a) * (bh ++ b) := by
  apply BitVec.eq_of_toNat_eq
  have pair (h l : BitVec 32) : (h ++ l).toNat = h.toNat * 2 ^ 32 + l.toNat := by
    rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt l.isLt, Nat.shiftLeft_eq]
  rw [pair, BitVec.toNat_mul, pair, pair]
  simp only [BitVec.toNat_add, BitVec.toNat_mul]
  have bound := lo.isLt
  have expand : (ah.toNat * 2 ^ 32 + a.toNat) * (bh.toNat * 2 ^ 32 + b.toNat) =
      lo.toNat + (hi.toNat + a.toNat * bh.toNat + b.toNat * ah.toNat) * 2 ^ 32 +
        ah.toNat * bh.toNat * 2 ^ 64 := by
    rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by decide]
    grind
  rw [expand, Nat.add_mul_mod_self_right]
  rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by decide, Nat.mod_mul,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt bound,
    Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt bound, Nat.zero_add]
  simp only [Nat.add_mod, Nat.mod_mod, Nat.mul_mod]
  omega

end VG.Proof.Bignum.Arm
