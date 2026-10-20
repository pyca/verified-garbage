module
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.Omega

/-! The right-to-left byte borrow used by scalar rejection sampling. -/
@[expose] public section
namespace VG.Proof.Dsa
open VG

/-- Borrow after subtracting equal-width big-endian byte strings. -/
def randomBorrow : List Byte → List Byte → Nat
  | a :: as, b :: bs => if a.toNat < b.toNat + randomBorrow as bs then 1 else 0
  | _, _ => 0

private theorem compare_digit (a b x y m : Nat) (hx : x < m) (hy : y < m) :
    (a < b + (if x < y then 1 else 0)) ↔ a * m + x < b * m + y := by
  by_cases hab : a < b
  · have hm := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hab)
    rw [Nat.succ_mul] at hm
    split <;> omega
  · by_cases he : a = b
    · subst a
      split <;> omega
    · have hm := Nat.mul_le_mul_right m (show b + 1 ≤ a by omega)
      rw [Nat.succ_mul] at hm
      split <;> omega

/-- The final borrow is exactly the unsigned comparison of the whole scalars. -/
theorem randomBorrow_eq (as bs : List Byte) (h : as.length = bs.length) :
    randomBorrow as bs = if Spec.Dsa.decodeBE as < Spec.Dsa.decodeBE bs then 1 else 0 := by
  induction as generalizing bs with
  | nil =>
    have hb : bs = [] := List.length_eq_zero_iff.mp h.symm
    subst bs
    rfl
  | cons a as ih =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      have hl : as.length = bs.length := by simpa only [List.length_cons, Nat.add_right_cancel_iff] using h
      rw [randomBorrow, ih bs hl]
      have hc := compare_digit a.toNat b.toNat (Spec.Dsa.decodeBE as) (Spec.Dsa.decodeBE bs)
        (256 ^ as.length) (decodeBE_lt as) (by rw [hl]; exact decodeBE_lt bs)
      have hda : Spec.Dsa.decodeBE (a :: as) = a.toNat * 256 ^ as.length + Spec.Dsa.decodeBE as := by
        rw [decodeBE_os2ip (a :: as), VG.Proof.RsaPss.os2ip_cons']; rfl
      have hdb : Spec.Dsa.decodeBE (b :: bs) = b.toNat * 256 ^ bs.length + Spec.Dsa.decodeBE bs := by
        rw [decodeBE_os2ip (b :: bs), VG.Proof.RsaPss.os2ip_cons']; rfl
      simp only [hda, hdb, ← hl, hc]

theorem randomBorrow_le (as bs : List Byte) : randomBorrow as bs ≤ 1 := by
  cases as with
  | nil => exact Nat.zero_le _
  | cons a as =>
    cases bs with
    | nil => exact Nat.zero_le _
    | cons b bs => unfold randomBorrow; split <;> decide

/-- OR accumulator in the order used by the right-to-left scan. -/
def randomOr : List Byte → BitVec 64
  | [] => 0
  | b :: bs => randomOr bs ||| b.setWidth 64

theorem randomOr_zero (bs : List Byte) : randomOr bs = 0 ↔ Spec.Dsa.decodeBE bs = 0 := by
  rw [decodeBE_eq_zero]
  induction bs with
  | nil => simp [randomOr]
  | cons b bs ih =>
    have hb : b.setWidth 64 = 0 ↔ b = 0 := by
      constructor
      · intro h
        apply BitVec.eq_of_toNat_eq
        have ht := congrArg BitVec.toNat h
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)] at ht
        exact ht
      · intro h; subst b; rfl
    change (randomOr bs ||| b.setWidth 64 = 0#64) ↔ _
    change randomOr bs = 0#64 ↔ _ at ih
    change b.setWidth 64 = 0#64 ↔ _ at hb
    rw [BitVec.or_eq_zero_iff, ih, hb]
    simp only [List.mem_cons, forall_eq_or_imp]
    exact and_comm

end VG.Proof.Dsa
