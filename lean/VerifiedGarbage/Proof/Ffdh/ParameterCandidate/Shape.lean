module

public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.RsaKeyGen.KeyCheck
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter candidates: exact bit widths, including Sophie Germain q -/

@[expose] public section

namespace VG.Proof.Ffdh.ParameterCandidate

open VG VG.Spec.Ffdh
open VG.Proof.RsaKeyGen

/-- Setting the high and low bits gives an odd candidate of exactly bits bits. -/
theorem candidate_shape {bits : Nat} (hb : 2 ≤ bits) (x : Nat) :
    (candidateOf bits x) % 2 = 1 ∧ 2 ^ (bits - 1) ≤ candidateOf bits x ∧ candidateOf bits x < 2 ^ bits := by
  unfold candidateOf
  refine ⟨?_, Nat.le_trans Nat.right_le_or Nat.left_le_or, ?_⟩
  · rw [show (2 : Nat) = 2 ^ 1 from rfl, Nat.or_mod_two_pow]
    rcases Nat.mod_two_eq_zero_or_one (x % 2 ^ bits ||| 2 ^ (bits - 1)) with h | h <;> simp [h]
  · exact Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_lt_pow_right (by decide) (by omega))) (Nat.one_lt_two_pow (by omega))

/-- An odd number cannot equal the even lower endpoint of its bit interval. -/
theorem odd_above_power {p bits : Nat} (hb : 2 ≤ bits) (ho : p % 2 = 1) (hl : 2 ^ (bits - 1) ≤ p) :
    2 ^ (bits - 1) ≤ p - 1 := by
  have he : 2 ^ (bits - 1) = 2 ^ (bits - 2) * 2 := by
    rw [show bits - 1 = bits - 2 + 1 by omega, Nat.pow_succ]
  omega

theorem candidate_bitLength {bits : Nat} (hb : 2 ≤ bits) (x : Nat) :
    Spec.RsaKeyGen.bitLength (candidateOf bits x) = bits ∧
      Spec.RsaKeyGen.bitLength (candidateOf bits x - 1) = bits := by
  obtain ⟨ho, hl, hu⟩ := candidate_shape hb x
  have he : bits - 1 + 1 = bits := by omega
  exact ⟨by simpa only [he] using bitLength_of hl (by simpa only [he] using hu),
    by simpa only [he] using bitLength_of (odd_above_power hb ho hl) (by simpa only [he] using Nat.lt_of_le_of_lt (Nat.sub_le _ _) hu)⟩

/-- q has one fewer significant bit, even when p's width is not a whole byte or word. -/
theorem half_shape {bits p : Nat} (hb : 2 ≤ bits) (ho : p % 2 = 1)
    (hl : 2 ^ (bits - 1) ≤ p) (hu : p < 2 ^ bits) :
    2 ^ (bits - 2) ≤ (p - 1) / 2 ∧ (p - 1) / 2 < 2 ^ (bits - 1) := by
  have hp := odd_above_power hb ho hl
  have he1 : 2 ^ (bits - 1) = 2 ^ (bits - 2) * 2 := by
    rw [show bits - 1 = bits - 2 + 1 by omega, Nat.pow_succ]
  have he2 : 2 ^ bits = 2 ^ (bits - 1) * 2 := by
    exact (congrArg (fun n => 2 ^ n) (show bits = bits - 1 + 1 by omega)).trans (Nat.pow_succ _ _)
  omega

theorem half_bitLength {bits : Nat} (hb : 2 ≤ bits) (x : Nat) :
    Spec.RsaKeyGen.bitLength ((candidateOf bits x - 1) / 2) = bits - 1 := by
  obtain ⟨ho, hl, hu⟩ := candidate_shape hb x
  obtain ⟨hql, hqu⟩ := half_shape hb ho hl hu
  have he : bits - 2 + 1 = bits - 1 := by omega
  simpa only [he] using bitLength_of hql (by simpa only [he] using hqu)

/-- Witnesses for p use p's exact byte width. -/
theorem candidate_witnessOctets {bits : Nat} (hb : 2 ≤ bits) (x : Nat) :
    witnessOctets (candidateOf bits x) = (bits + 7) / 8 := by
  unfold witnessOctets
  rw [(candidate_bitLength hb x).2]

/-- Subtracting one preserves an odd q's significant width. -/
theorem half_pred_bitLength {bits : Nat} (hb : 3 ≤ bits) (x : Nat)
    (ho : ((candidateOf bits x - 1) / 2) % 2 = 1) :
    Spec.RsaKeyGen.bitLength ((candidateOf bits x - 1) / 2 - 1) = bits - 1 := by
  obtain ⟨hpo, hl, hu⟩ := candidate_shape (by omega : 2 ≤ bits) x
  obtain ⟨hql, hqu⟩ := half_shape (by omega) hpo hl hu
  have he : bits - 1 - 1 = bits - 2 := by omega
  have hlow := odd_above_power (by omega : 2 ≤ bits - 1) ho (by simpa only [he] using hql)
  have he' : bits - 2 + 1 = bits - 1 := by omega
  exact (bitLength_of (by simpa only [he] using hlow)
    (by rw [he']; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hqu)).trans he'

theorem half_witnessOctets {bits : Nat} (hb : 3 ≤ bits) (x : Nat)
    (ho : ((candidateOf bits x - 1) / 2) % 2 = 1) :
    witnessOctets ((candidateOf bits x - 1) / 2) = (bits - 1 + 7) / 8 := by
  unfold witnessOctets
  rw [half_pred_bitLength hb x ho]

/-- Candidate widths fit the FFDH contract and the shared Miller-Rabin workspace. -/
theorem candidate_widths {bits : Nat} (hlo : 512 ≤ bits) (hhi : bits ≤ 8192) :
    64 ≤ (bits + 7) / 8 ∧ (bits + 7) / 8 ≤ 1024 ∧
    64 ≤ (bits - 1 + 7) / 8 ∧ (bits - 1 + 7) / 8 ≤ (bits + 7) / 8 ∧
    (bits + 7) / 8 ≤ (bits - 1 + 7) / 8 + 1 ∧
    8 ≤ (bits + 63) / 64 ∧ (bits + 63) / 64 ≤ 128 ∧
    8 ≤ (bits - 1 + 63) / 64 ∧ (bits - 1 + 63) / 64 ≤ (bits + 63) / 64 := by
  omega

end VG.Proof.Ffdh.ParameterCandidate
