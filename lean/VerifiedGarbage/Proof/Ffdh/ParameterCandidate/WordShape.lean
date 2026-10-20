module
public import VerifiedGarbage.Spec.Ffdh

import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter candidates: each modulus's actual Montgomery word width -/

@[expose] public section

namespace VG.Proof.Ffdh.ParameterCandidate

open VG VG.Spec.Ffdh

/-- The exact word width, without requiring the highest word to be full. -/
theorem candidate_word_shape {bits : Nat} (hb : 2 ≤ bits) (x : Nat) :
    2 ^ (64 * ((bits + 63) / 64 - 1)) ≤ candidateOf bits x ∧
      candidateOf bits x < 2 ^ (64 * ((bits + 63) / 64)) := by
  obtain ⟨_, hl, hu⟩ := candidate_shape hb x
  exact ⟨Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hl,
    Nat.lt_of_lt_of_le hu (Nat.pow_le_pow_right (by decide) (by omega))⟩

theorem half_word_shape {bits : Nat} (hb : 3 ≤ bits) (x : Nat) :
    2 ^ (64 * ((bits - 1 + 63) / 64 - 1)) ≤ (candidateOf bits x - 1) / 2 ∧
      (candidateOf bits x - 1) / 2 < 2 ^ (64 * ((bits - 1 + 63) / 64)) := by
  obtain ⟨ho, hl, hu⟩ := candidate_shape (by omega : 2 ≤ bits) x
  obtain ⟨hql, hqu⟩ := half_shape (by omega) ho hl hu
  exact ⟨Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hql,
    Nat.lt_of_lt_of_le hqu (Nat.pow_le_pow_right (by decide) (by omega))⟩

/-- The original p-sized buffer can load either modulus, using at most one
extra zero word in the q workspace. -/
theorem candidate_load_widths {bits : Nat} (hlo : 512 ≤ bits) (hhi : bits ≤ 8192) :
    (((bits + 7) / 8) + 7) / 8 = (bits + 63) / 64 ∧
      (bits - 1 + 63) / 64 ≤ (((bits + 7) / 8) + 7) / 8 ∧
      (((bits + 7) / 8) + 7) / 8 ≤ (bits - 1 + 63) / 64 + 1 ∧
      8 ≤ (bits - 1 + 63) / 64 ∧ (bits + 63) / 64 ≤ 128 := by omega

end VG.Proof.Ffdh.ParameterCandidate
