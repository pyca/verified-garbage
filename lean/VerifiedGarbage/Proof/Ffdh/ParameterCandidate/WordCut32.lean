module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Weierstrass.Words32
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! Cutting one occupied native word masks the complete packed integer,
including a partially occupied top word below the allocated width. -/

@[expose] public section
namespace VG.Proof.Ffdh.ParameterCandidate
open VG VG.Proof.Mont
open VG.Proof.Weierstrass (testBit_val32)

theorem testBit_mask32 {k : Nat} (bound : k ≤ 32) (i : Nat) :
    (BitVec.ofNat 32 (2 ^ k - 1)).toNat.testBit i = decide (i < k) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) bound
    have := Nat.two_pow_pos k
    omega), Nat.testBit_two_pow_sub_one]

theorem val32_cut {m m' : Mem} {base : Addr} {d w j k : Nat}
    (bits : k ≤ 32)
    (small : val32 m base d w < 2 ^ (32 * (j + 1)))
    (top : m'.readW (off base (d + 4 * j)) 32 =
      m.readW (off base (d + 4 * j)) 32 &&& BitVec.ofNat 32 (2 ^ k - 1))
    (other : ∀ i, i < w → i ≠ j →
      m'.readW (off base (d + 4 * i)) 32 = m.readW (off base (d + 4 * i)) 32) :
    val32 m' base d w = val32 m base d w % 2 ^ (32 * j + k) := by
  have topNat := congrArg BitVec.toNat top
  rw [BitVec.toNat_and] at topNat
  change w32 m' base (d + 4 * j) = w32 m base (d + 4 * j) &&& _ at topNat
  have otherNat (i : Nat) (bound : i < w) (different : i ≠ j) :
      w32 m' base (d + 4 * i) = w32 m base (d + 4 * i) :=
    congrArg BitVec.toNat (other i bound different)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow]
  by_cases within : i < 32 * w
  · have index : i / 32 < w := by omega
    have bit : i % 32 < 32 := Nat.mod_lt _ (by decide)
    have split : i = 32 * (i / 32) + i % 32 := by omega
    have readNew := testBit_val32 m' base d w (i / 32) (i % 32) index bit
    have readOld := testBit_val32 m base d w (i / 32) (i % 32) index bit
    rw [← split] at readNew readOld
    rw [readNew]
    by_cases atTop : i / 32 = j
    · rw [atTop, topNat, Nat.testBit_and, testBit_mask32 bits]
      rw [readOld, atTop]
      have same : decide (i % 32 < k) = decide (i < 32 * j + k) := decide_eq_decide.mpr (by omega)
      rw [same, Bool.and_comm]
    · rw [otherNat (i / 32) index atTop, ← readOld]
      by_cases below : i / 32 < j
      · have keep : i < 32 * j + k := by omega
        simp only [keep, decide_true, Bool.true_and]
      · have high : 32 * (j + 1) ≤ i := by omega
        have zero := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le small
          (Nat.pow_le_pow_right (by decide : 0 < 2) high))
        rw [zero]
        simp only [Bool.and_false]
  · have scale := Nat.pow_le_pow_right (by decide : 0 < 2) (show 32 * w ≤ i by omega)
    have oldZero := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (val32_lt m base d w) scale)
    have newZero := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (val32_lt m' base d w) scale)
    rw [oldZero, newZero]
    simp only [Bool.and_false]

end VG.Proof.Ffdh.ParameterCandidate
