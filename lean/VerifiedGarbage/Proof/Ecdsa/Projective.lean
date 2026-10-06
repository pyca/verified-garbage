import VerifiedGarbage.Proof.Weierstrass.Law

namespace VG.Proof.Ecdsa
open Spec.Weierstrass VG.Proof.Weierstrass

/-- When `p ≤ 2n`, an affine coordinate can have only two lifts of a scalar. -/
theorem scalar_lifts {p n x r : Nat} (hpn : p ≤ 2 * n) (hx : x < p) (hr : r < n) :
    x % n = r ↔ x = r ∨ x = r + n := by
  by_cases hxn : x < n
  · rw [Nat.mod_eq_of_lt hxn]
    omega
  · have hn : n ≤ x := by omega
    rw [Nat.mod_eq_sub_mod hn, Nat.mod_eq_of_lt (show x - n < n by omega)]
    omega

/-- Multiplication by nonzero projective `Z` replaces affine division. -/
theorem projective_x_eq {C : Curve} (hC : Law C) {X Z a : Fe C} (hZ : Z ≠ 0) :
    X * Z ^ (C.p - 2) = a ↔ X = a * Z := by
  have hzInv : (1 : Fe C) = Z * Z ^ (C.p - 2) :=
    hC.x_eq (X := Z) (Y := Z) (Z := Z) (x := 1) (y := 1) ⟨hZ, by grind, by grind⟩
  constructor
  · intro h
    calc X = (X * Z ^ (C.p - 2)) * Z := by grind
         _ = a * Z := by rw [h]
  · intro h
    rw [h]
    grind

theorem projective_lift_eq {C : Curve} (hC : Law C) {X Z : Fe C} (hZ : Z ≠ 0)
    {a : Nat} (ha : a < C.p) :
    (X * Z ^ (C.p - 2)).val = a ↔ X = Fin.ofNat C.p a * Z := by
  have e := projective_x_eq hC (X := X) (a := Fin.ofNat C.p a) hZ
  rw [Fin.ext_iff, Fin.val_ofNat, Nat.mod_eq_of_lt ha] at e
  exact e

/-- The comparison needed by ECDSA, with the second lift admitted only below `p`. -/
theorem projective_matches {C : Curve} (hC : Law C) (hnp : C.n < C.p)
    (hpn : C.p ≤ 2 * C.n) {X Z : Fe C} (hZ : Z ≠ 0) {r : Nat} (hr : r < C.n) :
    Fin.ofNat C.n (X * Z ^ (C.p - 2)).val = Fin.ofNat C.n r ↔
      X = Fin.ofNat C.p r * Z ∨
        (r < C.p - C.n ∧ X = (Fin.ofNat C.p r + Fin.ofNat C.p C.n) * Z) := by
  rw [Fin.ext_iff, Fin.val_ofNat, Fin.val_ofNat, Nat.mod_eq_of_lt hr,
    scalar_lifts hpn (X * Z ^ (C.p - 2)).isLt hr]
  have hrp : r < C.p := Nat.lt_trans hr hnp
  have hfirst := projective_lift_eq hC (X := X) hZ hrp
  have hadd : Fin.ofNat C.p (r + C.n) = Fin.ofNat C.p r + Fin.ofNat C.p C.n := by
    apply Fin.ext
    simp only [Fin.val_ofNat, Fin.val_add]
    exact Nat.add_mod r C.n C.p
  constructor
  · rintro (h | h)
    · exact Or.inl (hfirst.mp h)
    · have hlt : r + C.n < C.p := h ▸ (X * Z ^ (C.p - 2)).isLt
      refine Or.inr ⟨by omega, ?_⟩
      rw [← hadd]
      exact (projective_lift_eq hC hZ hlt).mp h
  · rintro (h | ⟨hlt, h⟩)
    · exact Or.inl (hfirst.mpr h)
    · apply Or.inr
      apply (projective_lift_eq hC hZ (show r + C.n < C.p by omega)).mpr
      rw [hadd]
      exact h

end VG.Proof.Ecdsa
