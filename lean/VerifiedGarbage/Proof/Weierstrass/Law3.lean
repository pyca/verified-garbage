import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.Env

/-!
# The group law for `a = -3`

For a curve whose `a` is `-3` (`AM3`), Algorithm 4 of Renes, Costello and
Batina is Algorithm 1 (`rcbAdd3_eq`), so it maps representatives of two points
to one of their sum (`Law.add3`); Algorithm 6 is Algorithm 1's sum of a point
and itself on the curve (`rcbDbl3_eq`), and a representative of a point of
the curve satisfies the projective equation (`Rep.proj`), so it maps a
representative of a point to one of its double (`Law.dbl3`).
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

variable {C : Curve}

/-- The curve's `a` is `-3`. -/
def AM3 (C : Curve) : Prop := (Fin.ofNat C.p C.a : Fe C) = -3

theorem ofNat_three_mul (C : Curve) : (Fin.ofNat C.p (3 * C.b) : Fe C) = 3 * Fin.ofNat C.p C.b := by
  rw [ofNat_mul']
  congr 1

/-- A representative of a point of the curve satisfies `Y²Z = X³ + aXZ² + bZ³`. -/
theorem Rep.proj {X Y Z : Fe C} {P : Point C} (h : Rep C X Y Z P) (hP : onCurve C P = true) :
    Y * Y * Z = X * X * X + Fin.ofNat C.p C.a * X * Z * Z + Fin.ofNat C.p C.b * Z * Z * Z := by
  cases P with
  | infinity =>
    obtain ⟨hX, -, hZ⟩ := h
    rw [hX, hZ]; grind
  | affine x y =>
    obtain ⟨-, hX, hY⟩ := h
    simp only [onCurve, decide_eq_true_eq] at hP
    rw [hX, hY]
    have : y * y * Z * Z * Z = (x * x * x + Fin.ofNat C.p C.a * x + Fin.ofNat C.p C.b) * Z * Z * Z := by
      rw [hP]
    grind

/-- Algorithm 4 adds. -/
theorem Law.add3 (hC : Law C) (ha : AM3 C) {P Q : Point C} (hP : onCurve C P = true)
    (hQ : onCurve C Q = true) {X1 Y1 Z1 X2 Y2 Z2 X3 Y3 Z3 : Fe C} (h1 : Rep C X1 Y1 Z1 P)
    (h2 : Rep C X2 Y2 Z2 Q) (h : rcbAdd3 (Fin.ofNat C.p C.b) X1 Y1 Z1 X2 Y2 Z2 = (X3, Y3, Z3)) :
    Rep C X3 Y3 Z3 (Spec.Weierstrass.add P Q) := by
  refine hC.add hP hQ h1 h2 ?_
  show rcbAdd (Fin.ofNat C.p C.a) (Fin.ofNat C.p (3 * C.b)) X1 Y1 Z1 X2 Y2 Z2 = _
  rw [ha, ofNat_three_mul, ← rcbAdd3_eq, h]

/-- Algorithm 6 doubles. -/
theorem Law.dbl3 (hC : Law C) (ha : AM3 C) {P : Point C} (hP : onCurve C P = true)
    {X Y Z X3 Y3 Z3 : Fe C} (h1 : Rep C X Y Z P)
    (h : rcbDbl3 (Fin.ofNat C.p C.b) X Y Z = (X3, Y3, Z3)) :
    Rep C X3 Y3 Z3 (Spec.Weierstrass.add P P) := by
  have hE := h1.proj hP
  rw [ha] at hE
  refine hC.add hP hP h1 h1 ?_
  show rcbAdd (Fin.ofNat C.p C.a) (Fin.ofNat C.p (3 * C.b)) X Y Z X Y Z = _
  rw [ha, ofNat_three_mul, ← rcbDbl3_eq _ _ _ _ (by grind), h]

end VG.Proof.Weierstrass
