module

public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.Framework.Omega
public import Mathlib.Data.Nat.ModEq

/-! # Bounds and preservation ranges for the i686 Miller–Rabin adapter -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)
open VG.Spec.Rsa.MontMul (scratchBytes Apart)

def scratch (w : Nat) : Nat := 256 + 16 * w

theorem scratch_start (w : Nat) : scratch w + 32 = arrAt w 2 := by
  simp only [scratch, arrAt, Spec.Rsa.Mont.hdrBytes]; omega

theorem scratch_end (w : Nat) : scratch w + scratchBytes w + 24 = arrAt w 5 := by
  simp only [scratch, scratchBytes, arrAt, Spec.Rsa.Mont.hdrBytes]; omega

theorem scratch_after_modulus {w : Nat} : arrAt w 0 + 8 * w ≤ scratch w := by
  simp only [scratch, arrAt, Spec.Rsa.Mont.hdrBytes]; omega

theorem scratch_after_inverse {w : Nat} : 56 + 4 ≤ scratch w := by
  simp only [scratch]; omega

theorem array_monotone (w : Nat) {a b : Nat} (h : a ≤ b) : arrAt w a ≤ arrAt w b := by
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem scratch_before_operand (w : Nat) {j : Nat} (hj : 5 ≤ j) :
    scratch w + scratchBytes w ≤ arrAt w j := by
  have := scratch_end w
  have := array_monotone w hj
  omega

theorem operand_apart_scratch (w : Nat) {j : Nat} (hj : 5 ≤ j) :
    Apart (arrAt w j) (8 * w) (scratch w, scratchBytes w) := by
  exact Or.inr (scratch_before_operand w hj)

theorem modulus_apart_scratch (w : Nat) :
    Apart (arrAt w 0) (8 * w) (scratch w, scratchBytes w) :=
  Or.inl scratch_after_modulus

theorem inverse_apart_scratch (w : Nat) :
    Apart 56 4 (scratch w, scratchBytes w) := Or.inl scratch_after_inverse

/-- Every changed byte outside arrays 2 and 3 is in an explicitly saved
range. The saved array-4 prefix includes all its touched bytes. -/
theorem scratch_cover {w i : Nat}
    (lo : scratch w ≤ i) (hi : i < scratch w + scratchBytes w) :
    (scratch w ≤ i ∧ i < scratch w + 32) ∨
    (arrAt w 2 ≤ i ∧ i < arrAt w 4) ∨
    (arrAt w 4 ≤ i ∧ i < arrAt w 4 + 8 * w) := by
  simp only [scratch, scratchBytes, arrAt, Spec.Rsa.Mont.hdrBytes] at *
  omega

theorem saved_tail_in_array_one {w : Nat} (hw : 4 ≤ w) :
    arrAt w 1 ≤ scratch w ∧ scratch w + 32 = arrAt w 2 := by
  constructor
  · simp only [scratch, arrAt, Spec.Rsa.Mont.hdrBytes]; omega
  · exact scratch_start w

theorem saved_array_fits_frame {w : Nat} (hw : w ≤ 128) :
    savedArray + 8 * w ≤ frameBytes := by
  simp only [savedArray, frameBytes]; omega

theorem saved_ranges_disjoint : savedTail + 32 ≤ savedArray := by decide

theorem args_before_saved : 36 ≤ savedTail := by decide

theorem frame_valid : 0 < frameBytes ∧ frameBytes < 4096 ∧ frameBytes % 4 = 0 := by decide

theorem array_fits_bytes {w bytes j : Nat} (hf : arrAt w 28 ≤ bytes) (hj : j < 28) :
    arrAt w j + 8 * (w + 2) ≤ bytes := by
  have h := array_monotone w (show j + 1 ≤ 28 by omega)
  simp only [arrAt, Nat.add_mul, Nat.one_mul] at h hf ⊢
  omega

theorem array_fits {w len j : Nat} (hf : arrAt w 28 ≤ 8 * len) (hj : j < 28) :
    arrAt w j + 8 * (w + 2) ≤ 8 * len := array_fits_bytes hf hj

theorem scratch_fits {w len : Nat} (hf : arrAt w 28 ≤ 8 * len) :
    scratch w + scratchBytes w ≤ 8 * len := by
  have := scratch_end w
  have := array_monotone w (show 5 ≤ 28 by decide)
  omega

theorem operand_apart_modulus (w : Nat) {j : Nat} (hj : 5 ≤ j) :
    Apart (arrAt w j) (8 * w) (arrAt w 0, 8 * w) := by
  right
  exact Nat.le_trans scratch_after_modulus
    (Nat.le_trans (Nat.le_add_right _ _) (scratch_before_operand w hj))

theorem operand_apart_inverse (w : Nat) {j : Nat} (hj : 5 ≤ j) :
    Apart (arrAt w j) (8 * w) (56, 4) := by
  right
  exact Nat.le_trans scratch_after_inverse
    (Nat.le_trans (Nat.le_add_right _ _) (scratch_before_operand w hj))

end VG.Proof.MillerRabin.X86
