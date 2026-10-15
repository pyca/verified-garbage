module

public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Framework.Omega

/-! # Exact bit lengths as unsigned integer intervals -/

@[expose] public section
namespace VG.Proof.Dsa

theorem bitLength_iff_bounds {v bits : Nat} (hb : 0 < bits) :
    VG.Spec.Dsa.bitLength v = bits ↔ 2 ^ (bits - 1) ≤ v ∧ v < 2 ^ bits := by
  by_cases hv : v = 0
  · subst v
    have hp : 0 < 2 ^ (bits - 1) := Nat.pow_pos (by decide)
    simp only [VG.Spec.Dsa.bitLength, ite_true]
    omega
  · rw [VG.Spec.Dsa.bitLength, ite_eq_right hv]
    constructor
    · intro h
      exact ⟨(Nat.le_log2 hv).mp (by omega), (Nat.log2_lt hv).mp (by omega)⟩
    · intro ⟨lo, hi⟩
      have h1 := (Nat.le_log2 hv).mpr lo
      have h2 := (Nat.log2_lt hv).mpr hi
      omega

end VG.Proof.Dsa
