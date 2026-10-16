module

public import VerifiedGarbage.Proof.Bignum.Arm.ExponentTests
public import VerifiedGarbage.Proof.Bignum.Arm.ExponentWords
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The public-exponent decision matches the shared RSA limits exactly -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem exponentTest_ok (s : State) :
    WP isa exponentTest s fun t =>
      t.gpr .r7 = BitVec.ofNat 32
        (exponentBounds (s.gpr .r3) (s.gpr .r4) && !exponentIsOne (s.gpr .r3) (s.gpr .r4)).toNat ∧
      t.mem = s.mem ∧ Rest [.r5, .r7] s t := by
  rw [exponentTest, WP.seq_iff]
  refine WP.mono (exponentBoundsTest_ok s) ?_
  rintro u ⟨zero, memU, restU⟩
  refine WP.ite (exponentBounds (s.gpr .r3) (s.gpr .r4)) (by change some u.z = _; rw [zero]) ?_ ?_
  · intro bounds
    rw [WP.seq_iff]
    refine WP.mono (exponentOneTest_ok u) ?_
    rintro v ⟨one, memV, restV⟩
    rw [restU.gpr .r3 (by simp), restU.gpr .r4 (by simp)] at one
    refine WP.ite (exponentIsOne (s.gpr .r3) (s.gpr .r4)) (by change some v.z = _; rw [one]) ?_ ?_
    · intro invalid
      refine WP.mono (exponentResult_ok v false) ?_
      rintro t ⟨value, memT, restT⟩
      exact ⟨by simpa [bounds, invalid] using value, memT.trans (memV.trans memU), restU.trans (restV.trans restT)⟩
    · intro valid
      refine WP.mono (exponentResult_ok v true) ?_
      rintro t ⟨value, memT, restT⟩
      exact ⟨by simpa [bounds, valid] using value, memT.trans (memV.trans memU), restU.trans (restV.trans restT)⟩
  · intro invalid
    refine WP.mono (exponentResult_ok u false) ?_
    rintro t ⟨value, memT, restT⟩
    exact ⟨by simpa only [invalid, Bool.false_and] using value, memT.trans memU, restU.trans restT⟩

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

end VG.Proof.Bignum.Arm
