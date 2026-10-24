module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.CheckPrivate.Body
public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Status
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.Power
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicCT

/-!
# FFDH's key pairs on PPC64LE: the status

For a valid domain of `L` octets at `D`, `privateStatus` of y and x as the
code computes it: 2 unless `0 < x < bnd`, else 1 if `g^x mod p` is `good`
with y (not 0, 1 or `p − 1`, and y), else 0 (`privateStatus_dom`): with
`y = g^x mod p`, y is valid exactly when `g^x mod p` is in `2..p − 2`
(`publicValid_power`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.CheckPrivate

open VG VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt os2ip)
open VG.Proof.Mont (off)
open VG.Proof.Ffdh.PPC64LE.Derive (bnd)

/-- `privateStatus` for a valid domain of `L = 2 k` or `3 k` octets at `D`. -/
theorem privateStatus_dom {m : Mem} {D : Addr} {k L : Nat} (hk : 0 < k) (hL : L = 2 * k ∨ L = 3 * k)
    (hv : domainValid k (bytesAt m D L) = true) (y x : Nat) :
    privateStatus (domainOf k (bytesAt m D L)) y x =
      if ¬ (0 < x ∧ x < bnd m D k L (os2ip (bytesAt m D k))) then 2 else
        if good (os2ip (bytesAt m (off D k) k) ^ x % os2ip (bytesAt m D k)) (os2ip (bytesAt m D k)) y then 1
        else 0 := by
  have hpv : parametersValid (domainOf k (bytesAt m D L)) = true := by
    unfold domainValid at hv
    simp only [Bool.and_eq_true] at hv
    exact hv.1
  have h2k : 2 * k ≤ L := by omega
  have hmod := Proof.Ffdh.domainValid_mod hv
  have hp2 : 2 ≤ (domainOf k (bytesAt m D L)).p := (Proof.Ffdh.PPC64LE.Domain.modulus_facts hmod).1
  rw [Proof.Ffdh.privateStatus_eq hpv, Proof.Ffdh.PPC64LE.Derive.privateValid_dom hk hL]
  by_cases h : 0 < x ∧ x < bnd m D k L (os2ip (bytesAt m D k))
  · simp only [h, and_self, decide_true, Bool.true_eq_false, ↓reduceIte, not_true_eq_false]
    have hc : (publicValid ⟨domainOf k (bytesAt m D L), y⟩ = true ∧
        (domainOf k (bytesAt m D L)).g ^ x % (domainOf k (bytesAt m D L)).p = y) ↔
        good (os2ip (bytesAt m (off D k) k) ^ x % os2ip (bytesAt m D k)) (os2ip (bytesAt m D k)) y := by
      rw [← Proof.Ffdh.domainOf_p m D h2k, show os2ip (bytesAt m (off D k) k) = (domainOf k (bytesAt m D L)).g by
        rw [Proof.Ffdh.domainOf_g m D h2k]]
      have hz := Nat.mod_lt ((domainOf k (bytesAt m D L)).g ^ x) (show 0 < (domainOf k (bytesAt m D L)).p by omega)
      constructor
      · rintro ⟨hy, rfl⟩
        have := (Proof.Ffdh.publicValid_power hpv x).mp hy
        exact ⟨by omega, rfl⟩
      · rintro ⟨hr, rfl⟩
        exact ⟨(Proof.Ffdh.publicValid_power hpv x).mpr (by omega), rfl⟩
    by_cases hg : good (os2ip (bytesAt m (off D k) k) ^ x % os2ip (bytesAt m D k)) (os2ip (bytesAt m D k)) y
    · rw [ite_eq_left (hc.mpr hg), ite_eq_left hg]
    · rw [ite_eq_right (fun h' => hg (hc.mp h')), ite_eq_right hg]
  · simp [h]

end VG.Proof.Ffdh.PPC64LE.CheckPrivate
