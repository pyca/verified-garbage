module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Range
public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.Power
import VerifiedGarbage.Proof.Ffdh.KeyScalar

/-!
# FFDH's private keys on PPC64LE: the status

For a valid domain of `L` octets at `D`, `keyStatus` of x as the code
computes it: 2 unless `0 < x < bnd`, else 1 if `1 < g^x mod p < p − 1`, else 3
(`keyStatus_dom`); and the status is 2 exactly when x is out of range
(`keyStatus_two`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Derive

open VG VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt os2ip)
open VG.Proof.Mont (off)

/-- `privateValid` of a domain of `L = 2 k` or `3 k` octets at `D`. -/
theorem privateValid_dom {m : Mem} {D : Addr} {k L : Nat} (hk : 0 < k) (hL : L = 2 * k ∨ L = 3 * k) (x : Nat) :
    privateValid (domainOf k (bytesAt m D L)) x =
      decide (0 < x ∧ x < bnd m D k L (os2ip (bytesAt m D k))) := by
  unfold privateValid bnd
  rcases hL with rfl | rfl
  · rw [Proof.Ffdh.domainOf_q2 m D hk, ite_eq_right (show ¬ (2 * k = 3 * k) by omega),
      Proof.Ffdh.domainOf_p m D (by omega)]
    simp
  · rw [Proof.Ffdh.domainOf_q3 m D k, ite_eq_left rfl]
    simp [off]

/-- `keyStatus` for a valid domain of `L = 2 k` or `3 k` octets at `D`. -/
theorem keyStatus_dom {m : Mem} {D : Addr} {k L : Nat} (hk : 0 < k) (hL : L = 2 * k ∨ L = 3 * k)
    (hv : domainValid k (bytesAt m D L) = true) (x : Nat) :
    keyStatus (domainOf k (bytesAt m D L)) x =
      if ¬ (0 < x ∧ x < bnd m D k L (os2ip (bytesAt m D k))) then 2 else
        if 1 < os2ip (bytesAt m (off D k) k) ^ x % os2ip (bytesAt m D k) ∧
          os2ip (bytesAt m (off D k) k) ^ x % os2ip (bytesAt m D k) < os2ip (bytesAt m D k) - 1 then 1 else 3 := by
  have hpv : parametersValid (domainOf k (bytesAt m D L)) = true := by
    unfold domainValid at hv
    simp only [Bool.and_eq_true] at hv
    exact hv.1
  have h2k : 2 * k ≤ L := by omega
  simp only [Proof.Ffdh.KeyScalar.keyStatus_eq hpv, Proof.Ffdh.publicValid_power hpv, privateValid_dom hk hL]
  simp only [Proof.Ffdh.domainOf_p m D h2k, Proof.Ffdh.domainOf_g m D h2k]
  by_cases h : 0 < x ∧ x < bnd m D k L (os2ip (bytesAt m D k))
  · simp [h, off]
  · simp [h]

/-- The status is 2 exactly when x is out of range. -/
theorem keyStatus_two (a : Parameters) (x : Nat) : keyStatus a x = 2 ↔ privateValid a x = false := by
  unfold keyStatus
  cases privateValid a x
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    split <;> simp

end VG.Proof.Ffdh.PPC64LE.Derive
