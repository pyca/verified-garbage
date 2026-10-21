module

public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
import VerifiedGarbage.Proof.Framework.Omega

/-! Native 32-bit mask construction implements the shared first-octet
shaping rule, including an exact byte boundary. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG

private theorem topMask_nat (x j : Nat) :
    x % 2 ^ (j + 1) ||| 2 ^ j = x % 2 ^ j + 2 ^ j := by
  rw [← Nat.or_two_pow_eq_add_of_lt (Nat.mod_lt x (Nat.two_pow_pos j))]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
  by_cases same : i = j
  · simp [same]
  · have cut : (i < j + 1) = (i < j) := propext (by omega)
    simp only [cut]

theorem topMask_byte (b : Byte) {j : Nat} (bound : j < 8) :
    (((b.setWidth 32 &&& BitVec.ofNat 32 (2 ^ (j + 1) - 1)) |||
      BitVec.ofNat 32 (2 ^ j)).setWidth 8) = VG.Proof.Ffdh.ParameterCandidate.topByte j b := by
  have high : 2 ^ j < 256 := Nat.pow_lt_pow_right (by decide) bound
  have full : 2 ^ (j + 1) ≤ 256 := Nat.pow_le_pow_right (n := 2) (i := j + 1) (j := 8) (by decide) (by omega)
  have byte := b.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_and,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : 2 ^ (j + 1) - 1 < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : 2 ^ j < 2 ^ 32), Nat.and_two_pow_sub_one_eq_mod,
    topMask_nat, VG.Proof.Ffdh.ParameterCandidate.topByte_value bound]
  apply Nat.mod_eq_of_lt
  have lo := Nat.mod_lt b.toNat (Nat.two_pow_pos j)
  have pow : 2 ^ (j + 1) = 2 ^ j * 2 := Nat.pow_succ 2 j
  omega

theorem maskTopWord {j : Nat} (bound : j < 8) :
    (BitVec.ofNat 32 (2 ^ (j + 1) - 1) >>> 1) + 1 = BitVec.ofNat 32 (2 ^ j) := by
  have full : 2 ^ (j + 1) ≤ 256 := Nat.pow_le_pow_right (n := 2) (i := j + 1) (j := 8) (by decide) (by omega)
  have pow : 2 ^ (j + 1) = 2 ^ j * 2 := Nat.pow_succ 2 j
  have positive := Nat.two_pow_pos j
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, show (1 : BitVec 32).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega : 2 ^ (j + 1) - 1 < 2 ^ 32), BitVec.toNat_ofNat]
  have half : (2 ^ (j + 1) - 1) / 2 ^ 1 + 1 = 2 ^ j := by omega
  rw [half]

end VG.Proof.Ffdh.Arm.ParameterCandidate
