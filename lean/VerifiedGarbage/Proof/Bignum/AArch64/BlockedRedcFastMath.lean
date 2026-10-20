module

public import VerifiedGarbage.Proof.Ed25519.Word64
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Impl.Bignum.AArch64.Core
import VerifiedGarbage.TCB.AArch64.Simd
import VerifiedGarbage.Proof.Bignum.AArch64.Run

/-! Carry identities for omitting the canceled low Montgomery word. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.BlockedRedcFast
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Ed25519.Word64
open VG.Proof.Bignum.AArch64

/-- The skipped low product is the additive inverse of the old low word. -/
theorem canceled_product (a inv n : Word)
    (hinv : (n.toNat * inv.toNat + 1) % 2 ^ 64 = 0) :
    a * inv * n = -a := by
  have h := mont_low a.toNat inv.toNat n.toNat hinv
  have hz : a * inv * n + a = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul,
      Nat.add_mod, Nat.mul_mod, Nat.mod_mod] at h ⊢
    exact h
  generalize a * inv * n = b at hz ⊢
  bv_omega

/-- For a canceled word, the carry is exactly the nonzero test. -/
theorem canceled_carry (a : Word) : carryOut a (-a) false = decide (1 ≤ a.toNat) := by
  have ha := a.isLt
  simp only [carryOut, Bool.toNat_false, Nat.add_zero, BitVec.toNat_neg]
  rw [decide_eq_decide]
  omega

theorem canceled_sum (a : Word) : addCarry a (-a) false = 0 := by
  rw [addCarry_false, BitVec.add_right_neg]
  rfl

theorem canceled_flag (a : Word) :
    decide (2 ^ 64 ≤ a.toNat + (~~~BitVec.setWidth 64 1#16).toNat + true.toNat) =
      decide (2 ^ 64 ≤ a.toNat + (-a).toNat + false.toNat) := by
  have ha := a.isLt
  change decide (2 ^ 64 ≤ a.toNat + 18446744073709551614 + 1) =
    decide (2 ^ 64 ≤ a.toNat + (-a).toNat + 0)
  simp only [BitVec.toNat_neg, Nat.add_zero, decide_eq_decide]
  omega

end VG.Proof.Bignum.AArch64.BlockedRedcFast
