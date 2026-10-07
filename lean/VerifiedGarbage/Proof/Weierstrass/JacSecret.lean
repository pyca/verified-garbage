import VerifiedGarbage.Proof.Weierstrass.JacAdd

/-! Jacobian addition with infinity masks and no equal-point fallback. -/
namespace VG.Proof.Weierstrass
open Spec.Weierstrass
variable {C : Curve}

/-- The selection order matches the two branchless infinity masks. -/
def jacAddMasked (X1 Y1 Z1 X2 Y2 Z2 : Fe C) : Fe C × Fe C × Fe C :=
  if Z2 = 0 then (X1,Y1,Z1)
  else if Z1 = 0 then (X2,Y2,Z2)
  else jacAddF X1 Y1 Z1 X2 Y2 Z2

theorem InvJ.add_masked (hC : Law C) (ha : AM3 C) {X1 Y1 Z1 X2 Y2 Z2 : Fe C}
    {P Q : Point C} (hP : onCurve C P = true) (hQ : onCurve C Q = true)
    (h1 : InvJ C X1 Y1 Z1 P) (h2 : InvJ C X2 Y2 Z2 Q)
    (hne : P ≠ .infinity → Q ≠ .infinity → P ≠ Q) :
    let j := jacAddMasked X1 Y1 Z1 X2 Y2 Z2
    InvJ C j.1 j.2.1 j.2.2 (Spec.Weierstrass.add P Q) := by
  dsimp only [jacAddMasked]
  split
  next hz2 =>
    rw [(h2.z_zero_iff hC).mp hz2]
    cases P <;> exact h1
  next hz2 =>
    split
    next hz1 =>
      rw [(h1.z_zero_iff hC).mp hz1]
      exact h2
    next hz1 =>
      by_cases hx : X2*(Z1*Z1)-X1*(Z2*Z2) = 0
      · have hy : Y2*Z1*(Z1*Z1)-Y1*Z2*(Z2*Z2) ≠ 0 := by
          intro hy
          exact hne (fun hp => hz1 ((h1.z_zero_iff hC).mpr hp))
            (fun hq => hz2 ((h2.z_zero_iff hC).mpr hq))
            (h1.same hC h2 hz1 hz2 hx hy)
        refine Or.inl ⟨h1.opposite hC hP hQ h2 hz1 hz2 hx hy, ?_⟩
        dsimp only [jacAddF]
        rw [hx]
        exact Lean.Grind.Semiring.mul_zero _
      · exact h1.add_ne hC ha hP hQ h2 hz1 hz2 hx

/-- ECDH needs only X/Z²; the unused Y coordinate need not be converted. -/
theorem InvJ.x_eq_square_z (hC : Law C) {X Y Z x y : Fe C}
    (h : InvJ C X Y Z (.affine x y)) : x = X * (Z * Z) ^ (C.p - 2) := by
  have hz : Z ≠ 0 := fun hz => by
    have he := (h.z_zero_iff hC).mp hz
    cases he
  have hr : Rep C X (y * (Z * Z)) (Z * Z) (.affine x y) :=
    ⟨hC.mul_ne_zero hz hz, (h.affine_coords hC).1, rfl⟩
  exact hr.x_eq hC

theorem InvJ.square_z_zero_iff (hC : Law C) {X Y Z : Fe C} {P : Point C}
    (h : InvJ C X Y Z P) : Z * Z = 0 ↔ P = .infinity := by
  constructor
  · intro hs
    apply (h.z_zero_iff hC).mp
    by_contra hz
    exact hC.mul_ne_zero hz hz hs
  · intro hp
    rw [(h.z_zero_iff hC).mpr hp]
    exact Lean.Grind.Semiring.mul_zero _

end VG.Proof.Weierstrass
