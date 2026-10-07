import VerifiedGarbage.Proof.Weierstrass.JacAdd

/-!
# Co-Z formulas in Jacobian coordinates

A Jacobian triple scaled by `(λ², λ³, λ)`, `λ ≠ 0`, stands for the same point
(`InvJ.rescale`). Two triples sharing `Z` (co-Z, Meloni 2007) add by ZADDU
(`zadduF`): the sum is the Jacobian addition `jacAddF` scaled by `Z³`, and the
first point, `(X1 C, Y1 (W1 - W2))` with the sum's `Z`, is itself scaled by
`X1 - X2` (`InvJ.zaddu`). The co-Z doubling of an affine point (DBLU) is the
Jacobian doubling with `Z = 1`, and the point itself scaled by the double's
`Z = 2y` (`InvJ.rescale`).
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

section
variable {F : Type _} [Lean.Grind.CommRing F]

/-- ZADDU: the sum of `(X1, Y1, Z)` and `(X2, Y2, Z)`, `(X3, Y3, Z3)`, and the
first point with `Z3`, `(W1, A1)`. -/
def zadduF (X1 Y1 X2 Y2 Z : F) : (F × F × F) × (F × F) :=
  let C := (X1 - X2) * (X1 - X2)
  let W1 := X1 * C
  let W2 := X2 * C
  let A1 := Y1 * (W1 - W2)
  let X3 := (Y1 - Y2) * (Y1 - Y2) - W1 - W2
  ((X3, (Y1 - Y2) * (W1 - X3) - A1, Z * (X1 - X2)), (W1, A1))

/-- ZADDU's sum is the Jacobian sum `(X2, Y2, Z) + (X1, Y1, Z)` scaled by `Z³`. -/
theorem zadduF_jac (X1 Y1 X2 Y2 Z : F) :
    let r := zadduF X1 Y1 X2 Y2 Z
    let j := jacAddF X2 Y2 Z X1 Y1 Z
    r.1.1 * (Z * Z * Z * (Z * Z * Z)) = j.1 * (1 * 1) ∧
      r.1.2.1 * (Z * Z * Z * (Z * Z * Z) * (Z * Z * Z)) = j.2.1 * (1 * 1 * 1) ∧
      r.1.2.2 * (Z * Z * Z) = j.2.2 * 1 := by
  dsimp only [zadduF, jacAddF]
  refine ⟨?_, ?_, ?_⟩ <;> grind

/-- ZADDU's first point is `(X1, Y1, Z)` scaled by `X1 - X2`. -/
theorem zadduF_first (X1 Y1 X2 Y2 Z : F) :
    let r := zadduF X1 Y1 X2 Y2 Z
    r.2.1 * (1 * 1) = X1 * ((X1 - X2) * (X1 - X2)) ∧
      r.2.2 * (1 * 1 * 1) = Y1 * ((X1 - X2) * (X1 - X2) * (X1 - X2)) ∧
      r.1.2.2 * 1 = Z * (X1 - X2) := by
  dsimp only [zadduF]
  refine ⟨?_, ?_, ?_⟩ <;> grind

end

variable {C : Curve}

/-- A triple and its multiple by `(λ², λ³, λ)`, for `λ ≠ 0`, stand for the same
point: here `(X', Y', Z')` scaled by `μ` is `(X, Y, Z)` scaled by `λ`. -/
theorem InvJ.rescale (hC : Law C) {X Y Z X' Y' Z' l m : Fe C} {Q : Point C} (h : InvJ C X Y Z Q)
    (hl : l ≠ 0) (hm : m ≠ 0) (hx : X' * (m * m) = X * (l * l)) (hy : Y' * (m * m * m) = Y * (l * l * l))
    (hz : Z' * m = Z * l) : InvJ C X' Y' Z' Q := by
  by_cases hZ' : Z' = 0
  · have hZ : Z = 0 := by
      by_contra h0
      exact hC.mul_ne_zero h0 hl (by rw [← hz, hZ']; grind)
    exact Or.inl ⟨(h.z_zero_iff hC).mp hZ, hZ'⟩
  · have hZ : Z ≠ 0 := fun h0 => hC.mul_ne_zero hZ' hm (by rw [hz, h0]; grind)
    have hm3 := cube_ne_zero hC hm
    refine Or.inr ((h.rep_of_ne hZ).of_cross hC (cube_ne_zero hC hZ') ?_ ?_)
    · apply cancel_right hC hm3
      calc X' * Z' * (Z * Z * Z) * (m * m * m) = X' * (m * m) * (Z' * m) * (Z * Z * Z) := by grind
        _ = X * (l * l) * (Z * l) * (Z * Z * Z) := by rw [hx, hz]
        _ = X * Z * ((Z * l) * (Z * l) * (Z * l)) := by grind
        _ = X * Z * ((Z' * m) * (Z' * m) * (Z' * m)) := by rw [hz]
        _ = X * Z * (Z' * Z' * Z') * (m * m * m) := by grind
    · apply cancel_right hC hm3
      calc Y' * (Z * Z * Z) * (m * m * m) = Y' * (m * m * m) * (Z * Z * Z) := by grind
        _ = Y * (l * l * l) * (Z * Z * Z) := by rw [hy]
        _ = Y * ((Z * l) * (Z * l) * (Z * l)) := by grind
        _ = Y * ((Z' * m) * (Z' * m) * (Z' * m)) := by rw [hz]
        _ = Y * (Z' * Z' * Z') * (m * m * m) := by grind

/-- ZADDU of triples of `P` and `Q` sharing `Z ≠ 0`, with `X1 ≠ X2`: a triple of
`Q + P` and one of `P` sharing its `Z`. -/
theorem InvJ.zaddu (hC : Law C) (ha : AM3 C) {X1 Y1 X2 Y2 Z : Fe C} {P Q : Point C}
    (hP : onCurve C P = true) (hQ : onCurve C Q = true) (h1 : InvJ C X1 Y1 Z P) (h2 : InvJ C X2 Y2 Z Q)
    (hz : Z ≠ 0) (hx : X1 - X2 ≠ 0) :
    InvJ C (zadduF X1 Y1 X2 Y2 Z).1.1 (zadduF X1 Y1 X2 Y2 Z).1.2.1 (zadduF X1 Y1 X2 Y2 Z).1.2.2
        (Spec.Weierstrass.add Q P) ∧
      InvJ C (zadduF X1 Y1 X2 Y2 Z).2.1 (zadduF X1 Y1 X2 Y2 Z).2.2 (zadduF X1 Y1 X2 Y2 Z).1.2.2 P := by
  have hh : X1 * (Z * Z) - X2 * (Z * Z) ≠ 0 := by
    have e : X1 * (Z * Z) - X2 * (Z * Z) = (X1 - X2) * (Z * Z) := by grind
    rw [e]; exact hC.mul_ne_zero hx (hC.mul_ne_zero hz hz)
  have hs := h2.add_ne hC ha hQ hP h1 hz hz hh
  obtain ⟨jx, jy, jz⟩ := zadduF_jac X1 Y1 X2 Y2 Z
  obtain ⟨fx, fy, fz⟩ := zadduF_first X1 Y1 X2 Y2 Z
  exact ⟨hs.rescale hC hC.one_ne_zero (cube_ne_zero hC hz) jx jy jz,
    h1.rescale hC hx hC.one_ne_zero fx fy fz⟩

end VG.Proof.Weierstrass
