module

public import VerifiedGarbage.Proof.Bignum.ExponentCheckMath
import VerifiedGarbage.Proof.Bignum.Words

/-! # Native-word arithmetic for the public-exponent accumulator -/

@[expose] public section

namespace VG.Proof.Bignum
open VG

theorem exponent_low_word (x : Nat) (b : Byte) :
    ((BitVec.ofNat 32 (x % 2 ^ 32) <<< 8) + b.setWidth 32) =
      BitVec.ofNat 32 ((256 * x + b.toNat) % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [Nat.shiftLeft_eq, Nat.mod_mod]
  rw [Nat.mod_eq_of_lt (by have := b.isLt; omega : b.toNat < 2 ^ 32)]
  rw [Nat.mod_add_mod, show 2 ^ 8 = 256 from rfl, Nat.mul_comm, exponentLow_step]

theorem exponent_high_word (x : Nat) :
    (BitVec.ofNat 32 (exponentHigh x) <<< 8) + (BitVec.ofNat 32 (x % 2 ^ 32) >>> 24) =
      BitVec.ofNat 32 (256 * exponentHigh x + x % 2 ^ 32 / 2 ^ 24) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mod_mod]
  have high := exponentHigh_bound x
  have low := Nat.mod_lt x (by decide : 0 < 2 ^ 32)
  omega

theorem exponent_high_zero (h : Nat) (hh : h < 2 ^ 32) :
    ((BitVec.ofNat 32 h >>> 1) == 0) = decide (h < 2) := by
  rw [Bool.beq_eq_decide_eq]
  apply decide_eq_decide.mpr
  rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hh]
  simp only [Nat.shiftRight_eq_div_pow]
  change h / 2 = 0 ↔ h < 2
  omega

end VG.Proof.Bignum
