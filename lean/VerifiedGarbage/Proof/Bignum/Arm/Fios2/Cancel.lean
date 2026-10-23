module

public import Init.Data.BitVec.Lemmas
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! A quotient `q = m' u` cancels the low word of `u + q m`. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2

theorem cancel_low {u q inv lo hi : BitVec 32} {m c : Nat} (hq : q = inv * u)
    (h : lo.toNat + 2 ^ 32 * hi.toNat = m * q.toNat + u.toNat + c) (hc : c = 0)
    (hinv : (m * inv.toNat + 1) % 2 ^ 32 = 0) : lo = 0 := by
  apply BitVec.eq_of_toNat_eq
  have cancel := VG.Proof.Bignum.Arm.mont_low u.toNat inv.toNat m hinv
  have qN : q.toNat = u.toNat * inv.toNat % 2 ^ 32 := by
    rw [hq, BitVec.toNat_mul, Nat.mul_comm]
  rw [qN, hc, Nat.add_zero] at h
  have lr := lo.isLt
  change lo.toNat = 0
  rw [Nat.mul_comm m] at h
  omega

end VG.Proof.Bignum.Arm.Fios2
