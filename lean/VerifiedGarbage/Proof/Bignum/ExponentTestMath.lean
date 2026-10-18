module

public import VerifiedGarbage.Proof.Bignum.ExponentWords

/-! # Word tests equivalent to the shared RSA public-exponent predicate -/

@[expose] public section
namespace VG.Proof.Bignum
open VG

def exponentBounds (lo hi : BitVec 32) : Bool :=
  ((hi >>> 1) ||| ((lo &&& 1) ^^^ 1)) == 0

def exponentIsOne (lo hi : BitVec 32) : Bool := ((lo ^^^ 1) ||| hi) == 0

theorem exponentBounds_words (x : Nat) :
    exponentBounds (BitVec.ofNat 32 (x % 2 ^ 32)) (BitVec.ofNat 32 (exponentHigh x)) =
      (decide (x < 2 ^ 33) && decide (x % 2 = 1)) := by
  have high := exponentHigh_bound x
  have low := Nat.mod_lt x (by decide : 0 < 2 ^ 32)
  rw [Bool.eq_iff_iff]
  simp only [exponentBounds, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
  change ((_ ||| _) : BitVec 32) = 0#32 ↔ _
  rw [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]
  rw [parity_word]
  simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.mod_mod]
  rw [Nat.mod_eq_of_lt (by omega : exponentHigh x < 2 ^ 32)]
  have parity : x % 2 ^ 32 % 2 = x % 2 := Nat.mod_mod_of_dvd x (by decide)
  simp only [parity]
  unfold exponentHigh
  change min 2 (x / 2 ^ 32) / 2 = 0 ∧ x % 2 % 2 ^ 32 = 1 ↔ x < 2 ^ 33 ∧ x % 2 = 1
  omega

theorem exponentIsOne_words (x : Nat) :
    exponentIsOne (BitVec.ofNat 32 (x % 2 ^ 32)) (BitVec.ofNat 32 (exponentHigh x)) = decide (x = 1) := by
  rw [Bool.eq_iff_iff]
  simp only [exponentIsOne, beq_iff_eq, decide_eq_true_eq]
  change ((_ ||| _) : BitVec 32) = 0#32 ↔ _
  rw [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]
  simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_mod]
  have high := exponentHigh_bound x
  rw [Nat.mod_eq_of_lt (by omega : exponentHigh x < 2 ^ 32)]
  unfold exponentHigh
  change x % 2 ^ 32 = 1 ∧ min 2 (x / 2 ^ 32) = 0 ↔ x = 1
  omega

theorem exponentTest_value (x : Nat) :
    (exponentBounds (BitVec.ofNat 32 (x % 2 ^ 32)) (BitVec.ofNat 32 (exponentHigh x)) &&
      !exponentIsOne (BitVec.ofNat 32 (x % 2 ^ 32)) (BitVec.ofNat 32 (exponentHigh x))) =
      Spec.Rsa.exponentValid x := by
  rw [exponentBounds_words, exponentIsOne_words, Bool.eq_iff_iff]
  simp [Spec.Rsa.exponentValid]
  omega

end VG.Proof.Bignum
