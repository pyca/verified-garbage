module
public import VerifiedGarbage.Spec.RsaPss
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.RsaPss.Params
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Dsa.Arithmetic

/-! # Actual modulus widths, independently of zero padding -/

@[expose] public section

namespace VG.Proof.Dsa
open VG

/-- The public scan returns the remaining length and first nonzero byte. -/
def significant : List Byte → Nat × Byte
  | [] => (0, 0)
  | b :: bs => if b = 0 then significant bs else (bs.length + 1, b)

theorem decodeBE_zero_cons (bs : List Byte) : Spec.Dsa.decodeBE (0 :: bs) = Spec.Dsa.decodeBE bs := rfl

/-- A nonzero first byte determines the bit length with the suffix length. -/
theorem bitLength_cons {b : Byte} (bs : List Byte) (hb : b ≠ 0) :
    Spec.Dsa.bitLength (Spec.Dsa.decodeBE (b :: bs)) = 8 * bs.length + b.toNat.log2 + 1 := by
  have hb' : b.toNat ≠ 0 := fun h => hb (BitVec.eq_of_toNat_eq h)
  have hpos : 0 < Spec.Dsa.decodeBE (b :: bs) := by
    rw [decodeBE_os2ip, VG.Proof.RsaPss.os2ip_cons']
    have : 0 < b.toNat * 256 ^ bs.length := Nat.mul_pos (by omega) (Nat.pow_pos (by decide))
    omega
  have h := VG.Proof.RsaPss.emBits_eq bs hb
  simp only [Spec.RsaPss.bitLength, Nat.add_sub_cancel] at h
  rw [Spec.Dsa.bitLength, ite_eq_right (by omega), decodeBE_os2ip, h]

/-- The scan is a bit-length calculation that also handles all-zero buffers. -/
theorem significant_bits (bs : List Byte) :
    Spec.Dsa.bitLength (Spec.Dsa.decodeBE bs) =
      if (significant bs).1 = 0 then 0 else
        8 * ((significant bs).1 - 1) + (significant bs).2.toNat.log2 + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    by_cases hb : b = 0
    · subst b
      rw [decodeBE_zero_cons, significant, ite_eq_left rfl]
      exact ih
    · rw [significant, ite_eq_right hb]
      dsimp only
      rw [ite_eq_right (Nat.succ_ne_zero _), Nat.add_sub_cancel]
      exact bitLength_cons bs hb

theorem significant_nonzero (bs : List Byte) : (significant bs).1 = 0 ↔ (significant bs).2 = 0 := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    by_cases hb : b = 0
    · rw [significant, ite_eq_left hb]; exact ih
    · rw [significant, ite_eq_right hb]
      dsimp only
      exact iff_of_false (Nat.succ_ne_zero _) hb

theorem significant_fits (bs : List Byte) : (significant bs).1 ≤ bs.length := by
  induction bs with
  | nil => exact Nat.le_refl _
  | cons b bs ih =>
    simp only [significant, List.length_cons]
    split
    · exact Nat.le_trans ih (Nat.le_succ _)
    · exact Nat.le_refl _

/-- A supported byte-aligned width is recognized exactly by the scan's
length and top-bit test. Padded smaller domains therefore stay admissible. -/
theorem significant_width (bs : List Byte) {n : Nat} (hn : 0 < n) :
    Spec.Dsa.bitLength (Spec.Dsa.decodeBE bs) = 8 * n ↔
      (significant bs).1 = n ∧ 128 ≤ (significant bs).2.toNat := by
  have ht := VG.Proof.RsaPss.log2_lt8 (significant bs).2
  rw [significant_bits]
  by_cases hz : (significant bs).1 = 0
  · rw [ite_eq_left hz]
    constructor
    · intro h; omega
    · intro h; omega
  · rw [ite_eq_right hz]
    have hb : (significant bs).2.toNat ≠ 0 := by
      intro hb
      have he : (significant bs).2 = 0 := BitVec.eq_of_toNat_eq hb
      exact hz ((significant_nonzero bs).mpr he)
    have he : 128 ≤ (significant bs).2.toNat ↔ 7 ≤ (significant bs).2.toNat.log2 := by
      change 2 ^ (7 : Nat) ≤ (significant bs).2.toNat ↔ 7 ≤ (significant bs).2.toNat.log2
      exact (Nat.le_log2 hb).symm
    rw [he]
    omega

end VG.Proof.Dsa
