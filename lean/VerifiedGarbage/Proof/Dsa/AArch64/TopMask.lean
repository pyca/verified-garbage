module
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp

import VerifiedGarbage.Proof.Dsa.AArch64.Masks
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Testing byte-aligned modulus bit lengths -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem byte_top_mask (b : Byte) :
    (0#64 - (BitVec.ofBool (decide ((b.zeroExtend 64).toNat < 128))).setWidth 64) ^^^ BitVec.allOnes 64 =
      mask (decide (128 ≤ b.toNat)) := by
  change mask (decide ((b.setWidth 64).toNat < 128)) ^^^ BitVec.allOnes 64 = _
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (show 2 ^ 8 < 2 ^ 64 by decide)),
    mask_complement, ← decide_not]
  exact congrArg mask (decide_eq_decide.mpr (by omega))

theorem byte_top_shift (b : Byte) :
    (0#64) - (b.zeroExtend 64 >>> 7) = mask (decide (128 ≤ b.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  by_cases h : 128 ≤ b.toNat
  all_goals simp [mask, h, BitVec.toNat_ushiftRight,
    BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
  all_goals omega

/-- The leading byte's high bit determines the exact byte-aligned width. -/
theorem topMask_ok {s : State} {b : Byte} (h9 : s.gpr .x10 = b.zeroExtend 64) :
    WP isa (.block VG.Impl.Dsa.AArch64.Checks.topMask) s fun t =>
      t.gpr .x3 = mask (decide (128 ≤ b.toNat)) ∧ t.mem = s.mem ∧ Keep [.x3, .x4] s t := by
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t =>
    t.gpr .x3 = mask (decide (128 ≤ b.toNat)) ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨ht, hm⟩, hk⟩ => ⟨ht, hm, hk⟩
  unfold VG.Impl.Dsa.AArch64.Checks.topMask
  brun [h9]
  exact byte_top_shift b

end VG.Proof.Dsa.AArch64
