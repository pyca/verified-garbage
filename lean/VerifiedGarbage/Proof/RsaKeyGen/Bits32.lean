module

public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.MillerRabin.ExponentWords32
import VerifiedGarbage.Proof.RsaKeyGen.Bits

/-! # Force the candidate bits using native 32-bit words -/

@[expose] public section
namespace VG.Proof.RsaKeyGen
open VG VG.Proof.Mont

theorem testBit_val32 (m : Mem) (p : Addr) (d n i : Nat) (index : i < 32 * n) :
    (val32 m p d n).testBit i = (w32 m p (d + 4 * (i / 32))).testBit (i % 32) := by
  rw [← VG.Proof.MillerRabin.val32_digit m p (by omega : i / 32 < n),
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp only [show i % 32 < 32 from Nat.mod_lt _ (by decide), decide_true, Bool.true_and]
  congr 1
  omega

theorem val32_candidate {m m' : Mem} {p : Addr} {d n : Nat} (positive : 2 ≤ n)
    (low : w32 m' p d = w32 m p d ||| 1)
    (top : w32 m' p (d + 4 * (n - 1)) = w32 m p (d + 4 * (n - 1)) ||| 3 * 2 ^ 30)
    (middle : ∀ j, 0 < j → j < n - 1 → w32 m' p (d + 4 * j) = w32 m p (d + 4 * j)) :
    val32 m' p d n = Spec.RsaKeyGen.candidate (32 * n) (val32 m p d n) := by
  apply Nat.eq_of_testBit_eq
  intro i
  unfold Spec.RsaKeyGen.candidate
  rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_mod_two_pow, testBit_three_mul]
  by_cases index : i < 32 * n
  · rw [testBit_val32 m' p d n i index, testBit_val32 m p d n i index]
    simp only [index, decide_true, Bool.true_and]
    by_cases first : i / 32 = 0
    · rw [first, Nat.mul_zero, Nat.add_zero, low, Nat.testBit_or,
        show i % 32 = i by omega, decide_eq_false (by omega : ¬ i = 32 * n - 2),
        decide_eq_false (by omega : ¬ i = 32 * n - 2 + 1)]
      simp
    · rw [testBit_one_ne (by omega : i ≠ 0)]
      by_cases last : i / 32 = n - 1
      · have e₁ : decide (i % 32 = 30) = decide (i = 32 * n - 2) := decide_eq_decide.mpr (by omega)
        have e₂ : decide (i % 32 = 30 + 1) = decide (i = 32 * n - 2 + 1) := decide_eq_decide.mpr (by omega)
        rw [last, top, Nat.testBit_or, testBit_three_mul, e₁, e₂]
        simp
      · rw [middle (i / 32) (by omega) (by omega),
          decide_eq_false (by omega : ¬ i = 32 * n - 2),
          decide_eq_false (by omega : ¬ i = 32 * n - 2 + 1)]
        simp
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (val32_lt m' p d n)
        (Nat.pow_le_pow_right (by decide) (by omega))), testBit_one_ne (by omega : i ≠ 0),
      decide_eq_false (by omega : ¬ i = 32 * n - 2),
      decide_eq_false (by omega : ¬ i = 32 * n - 2 + 1)]
    simp [index]

end VG.Proof.RsaKeyGen
