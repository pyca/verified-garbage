module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.RsaKeyGen.Bits32

/-! # The reviewed fallback witness from two native word updates -/

@[expose] public section
namespace VG.Proof.RsaKeyGen
open VG VG.Proof.Mont

theorem testBit_two (i : Nat) : Nat.testBit 2 i = decide (i = 1) := by
  rw [show (2 : Nat) = 2 ^ 1 from rfl, Nat.testBit_two_pow]
  exact decide_eq_decide.mpr eq_comm

theorem val32_witness_fallback {m m' : Mem} {p : Addr} {d n : Nat} (positive : 2 ≤ n)
    (low : w32 m' p d = w32 m p d ||| 2)
    (top : w32 m' p (d + 4 * (n - 1)) = w32 m p (d + 4 * (n - 1)) % 2 ^ 31)
    (middle : ∀ j, 0 < j → j < n - 1 → w32 m' p (d + 4 * j) = w32 m p (d + 4 * j)) :
    val32 m' p d n = (val32 m p d n ||| 2) % 2 ^ (32 * n - 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or, testBit_two]
  by_cases index : i < 32 * n
  · rw [testBit_val32 m' p d n i index, testBit_val32 m p d n i index]
    by_cases first : i / 32 = 0
    · rw [first, Nat.mul_zero, Nat.add_zero, low, Nat.testBit_or, testBit_two,
        show i % 32 = i by omega]
      simp only [show i < 32 * n - 1 by omega, decide_true, Bool.true_and]
    · by_cases last : i / 32 = n - 1
      · rw [last, top, Nat.testBit_mod_two_pow, decide_eq_false (by omega : i ≠ 1), Bool.or_false]
        rw [show decide (i % 32 < 31) = decide (i < 32 * n - 1) from decide_eq_decide.mpr (by omega)]
      · rw [middle (i / 32) (by omega) (by omega)]
        simp only [show i < 32 * n - 1 by omega, decide_true, Bool.true_and,
          decide_eq_false (by omega : i ≠ 1), Bool.or_false]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (val32_lt m' p d n)
      (Nat.pow_le_pow_right (by decide) (by omega))), decide_eq_false (by omega : ¬ i < 32 * n - 1), Bool.false_and]

end VG.Proof.RsaKeyGen
