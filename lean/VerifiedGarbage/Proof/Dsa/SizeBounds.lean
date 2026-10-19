module
public import VerifiedGarbage.Spec.Dsa

import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Arithmetic bounds implied by DSA's supported actual bit lengths -/

@[expose] public section

namespace VG.Proof.Dsa
open VG

theorem bitLength_mono {a b : Nat} (h : a ≤ b) : Spec.Dsa.bitLength a ≤ Spec.Dsa.bitLength b := by
  by_cases ha : a = 0
  · simp only [Spec.Dsa.bitLength, ha, ↓reduceIte, Nat.zero_le]
  have hb : b ≠ 0 := by omega
  simp only [Spec.Dsa.bitLength, ha, hb, ↓reduceIte]
  exact Nat.add_le_add_right ((Nat.le_log2 hb).mpr (Nat.le_trans ((Nat.le_log2 ha).mp (Nat.le_refl _)) h)) 1

theorem supported_bounds {p q : Nat}
    (h : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength p) (Spec.Dsa.bitLength q)) :
    1 < p ∧ 255 < q ∧ q < p := by
  have hbits : 1024 ≤ Spec.Dsa.bitLength p ∧ 160 ≤ Spec.Dsa.bitLength q ∧
      Spec.Dsa.bitLength q ≤ 256 := by unfold Spec.Dsa.supportedSizes at h; omega
  have hp : 1 < p := by
    by_contra hn
    have hh := bitLength_mono (show p ≤ 1 by omega)
    have he : Spec.Dsa.bitLength 1 = 1 := by decide
    omega
  have hq : 255 < q := by
    by_contra hn
    have hh := bitLength_mono (show q ≤ 255 by omega)
    have he : Spec.Dsa.bitLength 255 = 8 := by decide
    omega
  refine ⟨hp, hq, ?_⟩
  by_contra hn
  have hh := bitLength_mono (show p ≤ q by omega)
  omega

end VG.Proof.Dsa
