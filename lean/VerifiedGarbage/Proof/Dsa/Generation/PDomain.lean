module
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.RsaKeyGen.KeyCheck
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.BitLengthBounds

/-! # Full-width reduced p candidates satisfy the native primality preconditions -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG

structure PDomain (len value : Nat) : Prop where
  width : len = 128 ∨ len = 256 ∨ len = 384
  odd : value % 2 = 1
  lower : 2 ^ (8 * len - 1) ≤ value
  upper : value < 2 ^ (8 * len)

theorem pDomain_reduction {len x q : Nat} (hw : len = 128 ∨ len = 256 ∨ len = 384)
    (hx : x % 2 = 1) (hu : x < 2 ^ (8 * len))
    (hguard : ¬ x + 1 - x % (2 * q) < 2 ^ (8 * len - 1)) :
    PDomain len (x + 1 - x % (2 * q)) :=
  ⟨hw, pReduction_odd x q, Nat.le_of_not_gt hguard, Nat.lt_of_le_of_lt (pReduction_le hx).2 hu⟩

theorem PDomain.bits {len value : Nat} (h : PDomain len value) : Spec.Dsa.bitLength value = 8 * len := by
  apply (VG.Proof.Dsa.bitLength_iff_bounds (by rcases h.width with hh | hh | hh <;> omega)).mpr
  exact ⟨h.lower, h.upper⟩

theorem PDomain.predBits {len value : Nat} (h : PDomain len value) :
    Spec.RsaKeyGen.bitLength (value - 1) = 8 * len := by
  have hl : 2 ≤ 8 * len := by rcases h.width with hh | hh | hh <;> omega
  have hlo := VG.Proof.Ffdh.ParameterCandidate.odd_above_power hl h.odd h.lower
  have hb := VG.Proof.RsaKeyGen.bitLength_of hlo
    (show value - 1 < 2 ^ (8 * len - 1 + 1) by rw [Nat.sub_add_cancel (by omega : 1 ≤ 8 * len)]; omega_using [h.upper])
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ 8 * len)] using hb

theorem PDomain.draw {len value : Nat} (h : PDomain len value) :
    Spec.RsaKeyGen.witnessBytes value = len := by
  unfold Spec.RsaKeyGen.witnessBytes
  rw [h.predBits]
  rcases h.width with hh | hh | hh <;> rw [hh] <;> decide

theorem PDomain.large {len value : Nat} (h : PDomain len value) : 8161 < value := by
  have hb : 8161 < 2 ^ (8 * len - 1) := by
    apply Nat.lt_of_lt_of_le (show 8161 < 2 ^ 13 by decide)
    apply Nat.pow_le_pow_right (by decide)
    rcases h.width with hh | hh | hh <;> omega
  exact Nat.lt_of_lt_of_le hb h.lower

theorem PDomain.checks {len value : Nat} (h : PDomain len value) :
    Spec.Dsa.primeChecks (Spec.Dsa.bitLength value) = if len ≤ 256 then 64 else 128 := by
  rw [h.bits]
  rcases h.width with hh | hh | hh <;> rw [hh] <;> decide

theorem PDomain.policy {len value : Nat} (h : PDomain len value) :
    1024 < Spec.Dsa.bitLength value ↔ 16 < len / 8 := by
  rw [h.bits]
  rcases h.width with hh | hh | hh <;> rw [hh] <;> decide

end VG.Proof.Dsa.Generation
