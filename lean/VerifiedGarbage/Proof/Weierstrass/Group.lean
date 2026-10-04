import VerifiedGarbage.Proof.Weierstrass.LadderStep
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The specification's group law is Mathlib's

On a curve with no point of order 2 (`Good`), every point of the curve is
nonsingular, and `toW` maps the specification's points to the points of
Mathlib's Weierstrass curve `y² = x³ + a x + b` over `ZMod p`: the
specification's addition is Mathlib's (`toW_add`), so its multiples are
Mathlib's (`toW_mul`), the reflection `(x, -y)` is the negation (`toW_neg`),
and `toW` is injective on the curve (`toW_inj`). Mathlib's points form an
abelian group, so the specification's points are one too (`Good.group`), and
with the rest of the group law's facts this is the interface the proofs of the
code take (`Good.law`), which only a curve's own facts import.
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass WeierstrassCurve.Affine

variable {C : Curve}

section
variable [Fact C.p.Prime]

variable (C) in
/-- The curve over `ZMod p`, as Mathlib's Weierstrass curve. -/
abbrev wcC : WeierstrassCurve.Affine (ZMod C.p) :=
  wc (C.a : ZMod C.p) (C.b : ZMod C.p)

theorem equation_of_onCurve {x y : Fe C} (h : onCurve C (.affine x y) = true) :
    (wcC C).Equation (toF x) (toF y) :=
  wc_equation.mpr (onCurve_affine.mp h)

theorem negY_wcC (x y : ZMod C.p) : (wcC C).negY x y = -y := by
  simp [wcC, wc]

theorem y_ne_negY (hC : Good C) {x y : Fe C} (h : onCurve C (.affine x y) = true) :
    toF y ≠ (wcC C).negY (toF x) (toF y) := by
  rw [negY_wcC]
  intro h'
  have h2 : (2 : ZMod C.p) * toF y = 0 := by linear_combination h'
  rcases mul_eq_zero.mp h2 with h2 | h2
  · exact two_ne_zero' hC.two_lt h2
  · exact Weierstrass.y_ne_zero hC.noTwoTorsion (onCurve_affine.mp h) h2

theorem nonsingular_of_onCurve (hC : Good C) {x y : Fe C} (h : onCurve C (.affine x y) = true) :
    (wcC C).Nonsingular (toF x) (toF y) := by
  rw [nonsingular_iff']
  refine ⟨equation_of_onCurve h, Or.inr ?_⟩
  have := y_ne_negY hC h
  rw [negY_wcC] at this
  simp only [wcC, wc, zero_mul, add_zero]
  intro h2
  exact this (by linear_combination h2)

/-- A point of the specification as Mathlib's (`0` off the curve). -/
noncomputable def toW (hC : Good C) : Point C → (wcC C).Point
  | .infinity => 0
  | .affine x y =>
    if h : onCurve C (.affine x y) = true then .some (toF x) (toF y) (nonsingular_of_onCurve hC h)
    else 0

theorem toW_affine (hC : Good C) {x y : Fe C} (h : onCurve C (.affine x y) = true) :
    toW hC (.affine x y) = .some (toF x) (toF y) (nonsingular_of_onCurve hC h) := by
  rw [toW]
  simp only [h, ↓reduceDIte]

theorem some_eq {x₁ y₁ x₂ y₂ : ZMod C.p} {h₁ : (wcC C).Nonsingular x₁ y₁}
    {h₂ : (wcC C).Nonsingular x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : (wcC C).Point) = .some x₂ y₂ h₂ := by
  subst hx hy; rfl

/-- The specification's addition is Mathlib's. -/
theorem toW_add (hC : Good C) {P Q : Point C} (hP : onCurve C P = true)
    (hQ : onCurve C Q = true) : toW hC (add P Q) = toW hC P + toW hC Q := by
  match P, Q with
  | .infinity, Q => rw [toW, zero_add]; rfl
  | .affine x y, .infinity => rw [toW, add_zero]; rfl
  | .affine x₁ y₁, .affine x₂ y₂ =>
    have hS := hC.onCurve_add hP hQ
    rw [toW_affine hC hP, toW_affine hC hQ]
    by_cases hc : x₁ = x₂ ∧ y₂ = -y₁
    · obtain ⟨rfl, rfl⟩ := hc
      rw [add_neg, Point.add_of_Y_eq rfl (by rw [negY_wcC, toF_neg, neg_neg])]
      rfl
    by_cases hx : x₁ = x₂
    · subst hx
      obtain rfl : y₁ = y₂ := ((y_eq_or_eq_neg hP hQ).resolve_right (fun h => hc ⟨rfl, h⟩)).symm
      have hy : y₁ ≠ -y₁ := fun h => hc ⟨rfl, h⟩
      have hyW := y_ne_negY hC hP
      rw [Point.add_self_of_Y_ne hyW]
      have hl := toF_tangent_slope hC.two_lt (x₁ := x₁) (two_mul_ne_zero hy)
      have hsl : (wcC C).slope (toF x₁) (toF x₁) (toF y₁) (toF y₁) =
          toF ((3 * x₁ * x₁ + Fin.ofNat C.p C.a) * inv (2 * y₁)) := by
        rw [slope_of_Y_ne rfl hyW, negY_wcC, div_eq_iff (by
          rw [sub_neg_eq_add, ← two_mul]; exact two_mul_ne_zero hy)]
        simp only [wcC, wc]
        linear_combination -hl
      revert hS
      rw [add_tangent hy]
      intro hS
      rw [toW_affine hC hS]
      refine some_eq ?_ ?_
      · rw [addX, hsl]
        simp only [toF_sub, toF_mul, toF_ofNat' 2, wc]
        ring
      · rw [addY, negAddY, addX, hsl, negY_wcC]
        simp only [toF_sub, toF_mul, toF_ofNat' 2, wc]
        ring
    · have hl := toF_chord_slope hC.two_lt (y₁ := y₁) (y₂ := y₂) hx
      have hd : toF x₁ - toF x₂ ≠ 0 := fun h => hx (toF_injective (sub_eq_zero.mp h))
      have hsl : (wcC C).slope (toF x₁) (toF x₂) (toF y₁) (toF y₂) =
          toF ((y₂ - y₁) * inv (x₂ - x₁)) := by
        rw [slope_of_X_ne (fun h => hx (toF_injective h)), div_eq_iff hd]
        linear_combination hl
      revert hS
      rw [add_chord hx]
      intro hS
      rw [toW_affine hC hS, Point.add_of_X_ne (fun h => hx (toF_injective h))]
      refine some_eq ?_ ?_
      · rw [addX, hsl]
        simp only [toF_sub, toF_mul, wc]
        ring
      · rw [addY, negAddY, addX, hsl, negY_wcC]
        simp only [toF_sub, toF_mul, wc]
        ring

/-- The specification's multiples are Mathlib's. -/
theorem toW_mul (hC : Good C) {P : Point C} (hP : onCurve C P = true) :
    ∀ k, toW hC (mul k P) = k • toW hC P := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [mul]
    by_cases h0 : k = 0
    · simp only [h0, ↓reduceIte]; rw [zero_nsmul]; rfl
    simp only [h0, ↓reduceIte]
    have hm := hC.onCurve_mul hP (k / 2)
    have hd := hC.onCurve_add hm hm
    have IH := ih (k / 2) (by omega)
    split
    · rename_i h
      rw [toW_add hC hm hm, IH, ← add_smul]
      congr 1
      omega
    · rw [toW_add hC hd hP, toW_add hC hm hm, IH, ← add_smul, ← succ_nsmul]
      congr 1
      omega

/-- The reflection is the negation. -/
theorem toW_neg (hC : Good C) {P : Point C} (hP : onCurve C P = true) :
    toW hC (negPt P) = -toW hC P := by
  cases P with
  | infinity => rw [negPt, toW, neg_zero]
  | affine x y =>
    have hN : onCurve C (.affine x (-y)) = true := by
      rw [onCurve_affine, toF_neg] at *
      linear_combination hP
    rw [negPt, toW_affine hC hP, toW_affine hC hN, Point.neg_some]
    exact some_eq rfl (by rw [toF_neg, negY_wcC])

/-- `toW` is injective on the curve. -/
theorem toW_inj (hC : Good C) {P Q : Point C} (hP : onCurve C P = true)
    (hQ : onCurve C Q = true) (h : toW hC P = toW hC Q) : P = Q := by
  match P, Q with
  | .infinity, .infinity => rfl
  | .infinity, .affine x y =>
    rw [toW_affine hC hQ] at h; exact absurd h.symm (Point.some_ne_zero _)
  | .affine x y, .infinity =>
    rw [toW_affine hC hP] at h; exact absurd h (Point.some_ne_zero _)
  | .affine x₁ y₁, .affine x₂ y₂ =>
    rw [toW_affine hC hP, toW_affine hC hQ] at h
    obtain ⟨hx, hy⟩ := Point.some.inj h
    rw [toF_injective hx, toF_injective hy]

end

/-- On a curve the proofs apply to, the specification's group law is an
abelian group's. -/
theorem Good.group (hC : Good C) :
    ∃ (A : Type) (_ : Lean.Grind.IntModule A) (f : Point C → A), GroupRep C A f := by
  have : Fact C.p.Prime := ⟨hC.prime⟩
  refine ⟨_, inferInstance, toW hC, ⟨toW_add hC, fun hP k => ?_, toW_neg hC, toW_inj hC⟩⟩
  rw [toW_mul hC hP, ← natCast_zsmul]

theorem Good.law (hC : Good C) : Law C where
  one_ne_zero := hC.one_ne_zero_fe
  add := hC.rep_add
  onCurve_add := hC.onCurve_add
  onCurve_mul := hC.onCurve_mul
  step := hC.ladder_step
  x_eq := hC.rep_x_eq
  y_eq := hC.rep_y_eq
  group := hC.group

end VG.Proof.Weierstrass
