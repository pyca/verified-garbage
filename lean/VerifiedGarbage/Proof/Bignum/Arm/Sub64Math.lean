module
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp


/-! # Subtract a register pair from a zero-extended word -/

@[expose] public section

namespace VG.Proof.Bignum.Arm

theorem sub64_value (c lo hi : BitVec 32) :
    ((0 - hi - (if lo.toNat ≤ c.toNat then 0 else 1)) ++ (c - lo)) =
      ((0 : BitVec 32) ++ c) - (hi ++ lo) := by
  have pair (h l : BitVec 32) : (h ++ l).toNat = h.toNat * 2 ^ 32 + l.toNat := by
    rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt l.isLt, Nat.shiftLeft_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, pair, pair, pair]
  have hc := c.isLt
  have hl := lo.isLt
  have hh := hi.isLt
  by_cases h : lo.toNat ≤ c.toNat <;>
    simp only [h, ite_true, ite_false, BitVec.toNat_sub,
      show (0 : BitVec 32).toNat = 0 from rfl,
      show (1 : BitVec 32).toNat = 1 from rfl] <;> omega

end VG.Proof.Bignum.Arm
