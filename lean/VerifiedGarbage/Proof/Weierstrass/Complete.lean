module

public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Weierstrass.Field
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.Rcb
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-! ### `Weierstrass.Affine`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.RcbIdent`, which this module and modules that import it used -/

section

/-!
# Polynomial identities of the complete addition formulas

Over any commutative ring, for points of `y² = x³ + a x + b`: `rcbAdd` is
symmetric in its two points and bihomogeneous of bidegree `(2, 2)`, it maps
`(0 : Y₁ : 0)` and `(X₂ : Y₂ : Z₂)` to a multiple of `(X₂ : Y₂ : Z₂)`, and on
points with `Z = 1` its output is, modulo the curve equations, a multiple of
the affine sum: of the chord's sum for `x₁ ≠ x₂` (scaled by `d = x₂ - x₁`),
of the tangent's for doubling (scaled by `2y`), and `(0 : Y₃ : 0)` for
`P + (-P)`. The coefficients of the curve equations were found by
polynomial division (computer algebra) and are checked by
`linear_combination`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass

variable {F : Type*} [CommRing F]

theorem rcbAdd_comm (a b3 X1 Y1 Z1 X2 Y2 Z2 : F) :
    rcbAdd a b3 X1 Y1 Z1 X2 Y2 Z2 = rcbAdd a b3 X2 Y2 Z2 X1 Y1 Z1 := by
  simp only [rcbAdd, Prod.mk.injEq]
  exact ⟨by ring, by ring, by ring⟩

theorem rcbAdd_scale (a b3 x1 y1 Z1 x2 y2 Z2 : F) :
    rcbAdd a b3 (x1 * Z1) (y1 * Z1) Z1 (x2 * Z2) (y2 * Z2) Z2 =
      (Z1 ^ 2 * Z2 ^ 2 * (rcbAdd a b3 x1 y1 1 x2 y2 1).1,
        Z1 ^ 2 * Z2 ^ 2 * (rcbAdd a b3 x1 y1 1 x2 y2 1).2.1,
        Z1 ^ 2 * Z2 ^ 2 * (rcbAdd a b3 x1 y1 1 x2 y2 1).2.2) := by
  simp only [rcbAdd, Prod.mk.injEq]
  exact ⟨by ring, by ring, by ring⟩

/-- `O + Q`, with `O = (0 : Y₁ : 0)`. -/
theorem rcbAdd_zero_left (a b3 Y1 X2 Y2 Z2 : F) :
    rcbAdd a b3 0 Y1 0 X2 Y2 Z2 = (Y1 ^ 2 * Y2 * X2, Y1 ^ 2 * Y2 * Y2, Y1 ^ 2 * Y2 * Z2) := by
  simp only [rcbAdd, Prod.mk.injEq]
  exact ⟨by ring, by ring, by ring⟩

theorem rcbAdd_neg_x (a b x y : F) : (rcbAdd a (3 * b) x y 1 x (-y) 1).1 = 0 := by
  simp only [rcbAdd]
  ring

theorem rcbAdd_neg_z (a b x y : F) : (rcbAdd a (3 * b) x y 1 x (-y) 1).2.2 = 0 := by
  simp only [rcbAdd]
  ring

section
variable {a b x1 y1 x2 y2 : F} (h1 : y1 ^ 2 = x1 ^ 3 + a * x1 + b)
  (h2 : y2 ^ 2 = x2 ^ 3 + a * x2 + b)
include h1 h2

/-- `Z₃` is `d³` times the `y`-coordinate of `P - Q`. -/
theorem rcbAdd_chord_z : (rcbAdd a (3 * b) x1 y1 1 x2 y2 1).2.2 =
    (-y2 - y1) * ((x2 - x1) ^ 2 * x1 - ((-y2 - y1) ^ 2 - (x1 + x2) * (x2 - x1) ^ 2)) -
      y1 * (x2 - x1) ^ 3 := by
  simp only [rcbAdd]
  linear_combination (-y1 - 2*y2) * h1 + (-2*y1 - y2) * h2

theorem rcbAdd_chord_x : (x2 - x1) ^ 2 * (rcbAdd a (3 * b) x1 y1 1 x2 y2 1).1 =
    ((y2 - y1) ^ 2 - (x1 + x2) * (x2 - x1) ^ 2) * (rcbAdd a (3 * b) x1 y1 1 x2 y2 1).2.2 := by
  simp only [rcbAdd]
  linear_combination (-a*x1*y1 - a*x1*y2 - 2*a*x2*y1 + 3*a*x2*y2 - 3*b*y1 + 2*b*y2 - 
    3*x1^2*x2*y2 - 3*x1*x2^2*y1 + 3*x1*x2^2*y2 + 2*x2^3*y2 - y1^2*y2 + y1*y2^2 + 
    y2^3) * h1 + (4*a*x1*y1 - a*x1*y2 - a*x2*y1 - a*x2*y2 + 3*b*y1 - 2*b*y2 + 3*x1^3*y1 + 
    x1^3*y2 + 3*x1^2*x2*y1 - 3*x1^2*x2*y2 - 3*x1*x2^2*y1 - y1*y2^2) * h2

theorem rcbAdd_chord_y : (x2 - x1) ^ 3 * (rcbAdd a (3 * b) x1 y1 1 x2 y2 1).2.1 =
    ((y2 - y1) * ((x2 - x1) ^ 2 * x1 - ((y2 - y1) ^ 2 - (x1 + x2) * (x2 - x1) ^ 2)) -
      y1 * (x2 - x1) ^ 3) * (rcbAdd a (3 * b) x1 y1 1 x2 y2 1).2.2 := by
  simp only [rcbAdd]
  linear_combination (-a^2*x1^2 - 2*a^2*x1*x2 - 4*a*b*x1 - 2*a*b*x2 - 6*a*x1^2*x2^2 - 
    4*a*x1*x2^3 - a*x1*y1^2 + 5*a*x1*y2^2 + 4*a*x2^4 - 2*a*x2*y1^2 + 5*a*x2*y1*y2 - 
    3*a*x2*y2^2 - 3*b^2 - 12*b*x1*x2^2 + 6*b*x2^3 - 3*b*y1^2 + 5*b*y1*y2 + 2*b*y2^2 - 
    9*x1^2*x2^4 - 3*x1^2*x2*y1*y2 + 15*x1^2*x2*y2^2 + 6*x1*x2^5 - 3*x1*x2^2*y1^2 + 
    6*x1*x2^2*y1*y2 - 15*x1*x2^2*y2^2 + 2*x2^3*y1*y2 + 2*x2^3*y2^2 - y1^3*y2 + 
    2*y1^2*y2^2 - 2*y2^4) * h1 + (5*a^2*x1^2 - 3*a^2*x1*x2 + a^2*x2^2 + 7*a*b*x1 - 
    a*b*x2 + a*x1^4 + 14*a*x1^3*x2 - 9*a*x1^2*x2^2 - 5*a*x1*y1*y2 + a*x2*y2^2 + 3*b^2 - 
    6*b*x1^3 + 27*b*x1^2*x2 - 15*b*x1*x2^2 - 5*b*y1*y2 + b*y2^2 + 9*x1^5*x2 - 
    6*x1^4*x2^2 - 2*x1^3*y1*y2 - 2*x1^3*y2^2 - 6*x1^2*x2*y1*y2 + 3*x1^2*x2*y2^2 + 
    3*x1*x2^2*y1*y2 + y1*y2^3) * h2

end

section
variable {a b x y : F} (h : y ^ 2 = x ^ 3 + a * x + b)
include h

theorem rcbAdd_tangent_z : (rcbAdd a (3 * b) x y 1 x y 1).2.2 = 8 * y ^ 3 := by
  simp only [rcbAdd]
  linear_combination (-6*y) * h

theorem rcbAdd_tangent_x : (2 * y) ^ 2 * (rcbAdd a (3 * b) x y 1 x y 1).1 =
    ((3 * x ^ 2 + a) ^ 2 - 2 * x * (2 * y) ^ 2) * (rcbAdd a (3 * b) x y 1 x y 1).2.2 := by
  simp only [rcbAdd]
  linear_combination (6*a^2*y + 36*a*x^2*y + 54*x^4*y + 24*x*y^3) * h

theorem rcbAdd_tangent_y : (2 * y) ^ 3 * (rcbAdd a (3 * b) x y 1 x y 1).2.1 =
    ((3 * x ^ 2 + a) * ((2 * y) ^ 2 * x - ((3 * x ^ 2 + a) ^ 2 - 2 * x * (2 * y) ^ 2)) -
      y * (2 * y) ^ 3) * (rcbAdd a (3 * b) x y 1 x y 1).2.2 := by
  simp only [rcbAdd]
  linear_combination (-6*a^3*y - 54*a^2*x^2*y - 162*a*x^4*y + 48*a*x*y^3 + 72*b*y^3 - 
    162*x^6*y + 24*y^5) * h

/-- `Y₃` is `(2y)³` times the `y`-coordinate of `2P`. -/
theorem rcbAdd_neg_y : (rcbAdd a (3 * b) x y 1 x (-y) 1).2.1 =
    (3 * x ^ 2 + a) * ((2 * y) ^ 2 * x - ((3 * x ^ 2 + a) ^ 2 - 2 * x * (2 * y) ^ 2)) -
      y * (2 * y) ^ 3 := by
  simp only [rcbAdd]
  linear_combination (-3*a*x + 9*b - 27*x^3 + 9*y^2) * h

end

end VG.Proof.Weierstrass

end

end

/-!
# The affine group law and the complete formulas over a field

Over a field `F`, for the curve `y² = x³ + a x + b`: the chord and tangent
constructions give points of the curve (Mathlib's
`WeierstrassCurve.Affine.equation_add`, for `a₁ = a₂ = a₃ = 0`), and, if no
point of the curve has `y = 0` (no point of order 2) and `2 ≠ 0`, `rcbAdd` on
points with `Z = 1` gives a nonzero multiple of their sum: of the chord's sum
for `x₁ ≠ x₂`, of the tangent's for `P = Q`, and `(0 : Y₃ : 0)` with
`Y₃ ≠ 0` for `Q = -P`. The slopes are any `l` with `l (x₂ - x₁) = y₂ - y₁`
(or `l · 2y = 3x² + a`), so that callers can give them as quotients.
-/

@[expose] public section

namespace VG.Proof.Weierstrass

variable {F : Type*} [Field F] {a b : F}

/-- `y² = x³ + a x + b` as a Weierstrass curve. -/
def wc (a b : F) : WeierstrassCurve.Affine F :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := a, a₆ := b }

theorem wc_equation {x y : F} : (wc a b).Equation x y ↔ y ^ 2 = x ^ 3 + a * x + b := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [wc, zero_mul, add_zero]

section
open WeierstrassCurve.Affine

/-- The chord through two points of the curve meets it again in a point
whose reflection is on the curve. -/
theorem chord_on {x1 y1 x2 y2 l : F} (h1 : y1 ^ 2 = x1 ^ 3 + a * x1 + b)
    (h2 : y2 ^ 2 = x2 ^ 3 + a * x2 + b) (hx : x1 ≠ x2) (hl : l * (x2 - x1) = y2 - y1) :
    (l * (x1 - (l * l - x1 - x2)) - y1) ^ 2 =
      (l * l - x1 - x2) ^ 3 + a * (l * l - x1 - x2) + b := by
  classical
  have e := (wc a b).equation_add (wc_equation.mpr h1) (wc_equation.mpr h2)
    (fun h => hx h.1)
  have hs : (wc a b).slope x1 x2 y1 y2 = l := by
    rw [slope_of_X_ne hx, div_eq_iff (sub_ne_zero.mpr hx)]
    linear_combination hl
  rw [hs, wc_equation] at e
  simp only [addY, negY, negAddY, addX, wc, zero_mul, sub_zero, add_zero] at e
  linear_combination e

/-- The tangent at a point of the curve with `2y ≠ 0` meets it again in a
point whose reflection is on the curve. -/
theorem tangent_on {x y l : F} (h : y ^ 2 = x ^ 3 + a * x + b) (hy : 2 * y ≠ 0)
    (hl : l * (2 * y) = 3 * x ^ 2 + a) :
    (l * (x - (l * l - 2 * x)) - y) ^ 2 = (l * l - 2 * x) ^ 3 + a * (l * l - 2 * x) + b := by
  classical
  have hn : y ≠ (wc a b).negY x y := by
    simp only [negY, wc, zero_mul, sub_zero]
    intro h'; apply hy; linear_combination h'
  have e := (wc a b).equation_add (wc_equation.mpr h) (wc_equation.mpr h)
    (fun h' => hn h'.2)
  have hs : (wc a b).slope x x y y = l := by
    have hd : y - (wc a b).negY x y ≠ 0 := sub_ne_zero.mpr hn
    rw [slope_of_Y_ne rfl hn, div_eq_iff hd]
    simp only [negY, wc, zero_mul, sub_zero, mul_zero, add_zero]
    linear_combination -hl
  rw [hs, wc_equation] at e
  simp only [addY, negY, negAddY, addX, wc, zero_mul, sub_zero, add_zero] at e
  linear_combination e

end

/-! ## `rcbAdd` on points with `Z = 1` -/

section
variable (ht : ∀ x : F, x ^ 3 + a * x + b ≠ 0)
include ht

theorem y_ne_zero {x y : F} (h : y ^ 2 = x ^ 3 + a * x + b) : y ≠ 0 := by
  rintro rfl; exact ht x (by linear_combination -h)

/-- For `x₁ ≠ x₂`: a nonzero multiple of the chord's sum. -/
theorem rcbAdd_chord {x1 y1 x2 y2 l : F} (h1 : y1 ^ 2 = x1 ^ 3 + a * x1 + b)
    (h2 : y2 ^ 2 = x2 ^ 3 + a * x2 + b) (hx : x1 ≠ x2) (hl : l * (x2 - x1) = y2 - y1) :
    (rcbAdd a (3 * b) x1 y1 1 x2 y2 1).2.2 ≠ 0 ∧
    (rcbAdd a (3 * b) x1 y1 1 x2 y2 1).1 =
      (l * l - x1 - x2) * (rcbAdd a (3 * b) x1 y1 1 x2 y2 1).2.2 ∧
    (rcbAdd a (3 * b) x1 y1 1 x2 y2 1).2.1 =
      (l * (x1 - (l * l - x1 - x2)) - y1) * (rcbAdd a (3 * b) x1 y1 1 x2 y2 1).2.2 := by
  have hd : x2 - x1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  refine ⟨?_, ?_, ?_⟩
  · -- `Z₃ = d³ · y(P - Q)`, and `P - Q` is a point of the curve.
    have h2' : (-y2) ^ 2 = x2 ^ 3 + a * x2 + b := by linear_combination h2
    have hl' : (-y2 - y1) / (x2 - x1) * (x2 - x1) = -y2 - y1 := div_mul_cancel₀ _ hd
    have hon := chord_on h1 h2' hx hl'
    have hz := rcbAdd_chord_z h1 h2
    rw [← hl'] at hz
    rw [hz]
    intro h0
    have hy : (-y2 - y1) / (x2 - x1) * (x1 - ((-y2 - y1) / (x2 - x1) * ((-y2 - y1) / (x2 - x1)) -
        x1 - x2)) - y1 = 0 := by
      refine (mul_eq_zero.mp (?_ : (x2 - x1) ^ 3 * _ = 0)).resolve_left (pow_ne_zero 3 hd)
      linear_combination h0
    rw [hy] at hon
    exact y_ne_zero ht hon rfl
  · have e := rcbAdd_chord_x h1 h2
    rw [← hl] at e
    refine mul_left_cancel₀ (pow_ne_zero 2 hd) ?_
    linear_combination e
  · have e := rcbAdd_chord_y h1 h2
    rw [← hl] at e
    refine mul_left_cancel₀ (pow_ne_zero 3 hd) ?_
    linear_combination e

/-- For `P = Q`: a nonzero multiple of the tangent's sum. -/
theorem rcbAdd_tangent (h2 : (2 : F) ≠ 0) {x y l : F} (h : y ^ 2 = x ^ 3 + a * x + b)
    (hl : l * (2 * y) = 3 * x ^ 2 + a) :
    (rcbAdd a (3 * b) x y 1 x y 1).2.2 ≠ 0 ∧
    (rcbAdd a (3 * b) x y 1 x y 1).1 = (l * l - 2 * x) * (rcbAdd a (3 * b) x y 1 x y 1).2.2 ∧
    (rcbAdd a (3 * b) x y 1 x y 1).2.1 =
      (l * (x - (l * l - 2 * x)) - y) * (rcbAdd a (3 * b) x y 1 x y 1).2.2 := by
  have hy : 2 * y ≠ 0 := mul_ne_zero h2 (y_ne_zero ht h)
  refine ⟨?_, ?_, ?_⟩
  · rw [rcbAdd_tangent_z h, show (8 : F) * y ^ 3 = (2 * y) ^ 3 by ring]
    exact pow_ne_zero 3 hy
  · have e := rcbAdd_tangent_x h
    rw [← hl] at e
    refine mul_left_cancel₀ (pow_ne_zero 2 hy) ?_
    linear_combination e
  · have e := rcbAdd_tangent_y h
    rw [← hl] at e
    refine mul_left_cancel₀ (pow_ne_zero 3 hy) ?_
    linear_combination e

/-- For `Q = -P`: `(0 : Y₃ : 0)` with `Y₃ ≠ 0` (`Y₃` is `(2y)³` times the
`y`-coordinate of `2P`). -/
theorem rcbAdd_neg (h2 : (2 : F) ≠ 0) {x y : F} (h : y ^ 2 = x ^ 3 + a * x + b) :
    (rcbAdd a (3 * b) x y 1 x (-y) 1).1 = 0 ∧ (rcbAdd a (3 * b) x y 1 x (-y) 1).2.1 ≠ 0 ∧
    (rcbAdd a (3 * b) x y 1 x (-y) 1).2.2 = 0 := by
  refine ⟨rcbAdd_neg_x a b x y, ?_, rcbAdd_neg_z a b x y⟩
  have hy : 2 * y ≠ 0 := mul_ne_zero h2 (y_ne_zero ht h)
  have hl : (3 * x ^ 2 + a) / (2 * y) * (2 * y) = 3 * x ^ 2 + a := div_mul_cancel₀ _ hy
  have hon := tangent_on h hy hl
  have e := rcbAdd_neg_y h
  rw [← hl] at e
  rw [e]
  intro h0
  have hy2 : (3 * x ^ 2 + a) / (2 * y) * (x - ((3 * x ^ 2 + a) / (2 * y) *
      ((3 * x ^ 2 + a) / (2 * y)) - 2 * x)) - y = 0 := by
    refine (mul_eq_zero.mp (?_ : (2 * y) ^ 3 * _ = 0)).resolve_left (pow_ne_zero 3 hy)
    linear_combination h0
  rw [hy2] at hon
  exact y_ne_zero ht hon rfl

end

end VG.Proof.Weierstrass

end

end

/-!
# The complete formulas compute the specification's group law

On a
curve with no point of order 2 (`Good`), `rcbAdd` maps representatives of
two points of the curve to a representative of their sum by the
specification's `add` (`rcbAdd_rep`), whichever case of SEC 1's group law
applies: the formulas are complete. The sum of two points of the curve is on
the curve (`onCurve_add`).

The proofs are in `ZMod C.p`, a field, with the image there (`ZRep`) of a
triple over `Fin C.p` (`Rep`, `Law.lean`); the results over `Fin C.p` make
`Good.law` (`Group.lean`), which the proofs of the code take, so that
they need none of Mathlib's algebra.
-/

@[expose] public section

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

/-- `(X : Y : Z)` over `ZMod C.p` represents `P`. -/
def ZRep (C : Curve) (X Y Z : ZMod C.p) : Point C → Prop
  | .infinity => X = 0 ∧ Y ≠ 0 ∧ Z = 0
  | .affine x y => Z ≠ 0 ∧ X = toF x * Z ∧ Y = toF y * Z

/-- What the proofs need of a curve: a prime field of characteristic above 3,
and no point of order 2 (`x³ + a x + b` has no root). -/
structure Good (C : Curve) : Prop where
  prime : C.p.Prime
  gt3 : 3 < C.p
  noTwoTorsion : ∀ x : ZMod C.p, x ^ 3 + (C.a : ZMod C.p) * x + (C.b : ZMod C.p) ≠ 0

variable {C : Curve}

theorem Good.two_lt (hC : Good C) : 2 < C.p := by have := hC.gt3; omega_using [this]

theorem onCurve_affine {x y : Fe C} : onCurve C (.affine x y) = true ↔
    toF y ^ 2 = toF x ^ 3 + (C.a : ZMod C.p) * toF x + (C.b : ZMod C.p) := by
  simp only [onCurve, decide_eq_true_eq]
  rw [← toF_inj]
  simp only [toF_add, toF_mul, toF_ofNat]
  constructor <;> intro h <;> linear_combination h

/-! ## The cases of the group law -/

theorem add_affine (x₁ y₁ x₂ y₂ : Fe C) : add (.affine x₁ y₁) (.affine x₂ y₂) =
    if x₁ = x₂ ∧ y₂ = -y₁ then .infinity
    else if x₁ ≠ x₂ then
      let l := (y₂ - y₁) * inv (x₂ - x₁)
      let x₃ := l * l - x₁ - x₂
      .affine x₃ (l * (x₁ - x₃) - y₁)
    else
      let l := (3 * x₁ * x₁ + Fin.ofNat C.p C.a) * inv (2 * y₁)
      let x₃ := l * l - 2 * x₁
      .affine x₃ (l * (x₁ - x₃) - y₁) := rfl

theorem add_neg {x₁ y₁ : Fe C} : add (.affine x₁ y₁) (.affine x₁ (-y₁)) = .infinity := by
  rw [add_affine, ite_eq_left ⟨rfl, rfl⟩]

theorem add_chord {x₁ y₁ x₂ y₂ : Fe C} (hx : x₁ ≠ x₂) : add (.affine x₁ y₁) (.affine x₂ y₂) =
    .affine ((y₂ - y₁) * inv (x₂ - x₁) * ((y₂ - y₁) * inv (x₂ - x₁)) - x₁ - x₂)
      ((y₂ - y₁) * inv (x₂ - x₁) *
        (x₁ - ((y₂ - y₁) * inv (x₂ - x₁) * ((y₂ - y₁) * inv (x₂ - x₁)) - x₁ - x₂)) - y₁) := by
  rw [add_affine, ite_eq_right (fun h => hx h.1), ite_eq_left hx]

theorem add_tangent {x₁ y₁ : Fe C} (hy : y₁ ≠ -y₁) : add (.affine x₁ y₁) (.affine x₁ y₁) =
    .affine ((3 * x₁ * x₁ + Fin.ofNat C.p C.a) * inv (2 * y₁) *
        ((3 * x₁ * x₁ + Fin.ofNat C.p C.a) * inv (2 * y₁)) - 2 * x₁)
      ((3 * x₁ * x₁ + Fin.ofNat C.p C.a) * inv (2 * y₁) *
        (x₁ - ((3 * x₁ * x₁ + Fin.ofNat C.p C.a) * inv (2 * y₁) *
          ((3 * x₁ * x₁ + Fin.ofNat C.p C.a) * inv (2 * y₁)) - 2 * x₁)) - y₁) := by
  rw [add_affine, ite_eq_right (fun h => hy h.2), ite_eq_right (fun h => h rfl)]

section
variable [Fact C.p.Prime]

theorem two_ne_zero' (hp : 2 < C.p) : (2 : ZMod C.p) ≠ 0 := by
  intro h
  have : ((2 : Nat) : ZMod C.p) = ((0 : Nat) : ZMod C.p) := by rw [Nat.cast_ofNat, h, Nat.cast_zero]
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hp, Nat.zero_mod] at this
  exact absurd this (by decide)

/-- On the curve, points with the same `x` have `y₂ = ±y₁`. -/
theorem y_eq_or_eq_neg {x y₁ y₂ : Fe C} (h1 : onCurve C (.affine x y₁) = true)
    (h2 : onCurve C (.affine x y₂) = true) : y₂ = y₁ ∨ y₂ = -y₁ := by
  rw [onCurve_affine] at h1 h2
  have : (toF y₂ - toF y₁) * (toF y₂ + toF y₁) = 0 := by linear_combination h2 - h1
  rcases mul_eq_zero.mp this with h | h
  · exact .inl (toF_injective (sub_eq_zero.mp h))
  · exact .inr (toF_injective (by rw [toF_neg]; linear_combination h))

/-- The slope of the chord, in `ZMod C.p`. -/
theorem toF_chord_slope (hp : 2 < C.p) {x₁ y₁ x₂ y₂ : Fe C} (hx : x₁ ≠ x₂) :
    toF ((y₂ - y₁) * inv (x₂ - x₁)) * (toF x₂ - toF x₁) = toF y₂ - toF y₁ := by
  have hd : toF x₂ - toF x₁ ≠ 0 := fun h => hx (toF_injective (sub_eq_zero.mp h)).symm
  rw [toF_mul, toF_inv hp, toF_sub, toF_sub, inv_mul_cancel_right₀ hd]

/-- The slope of the tangent, in `ZMod C.p`. -/
theorem toF_tangent_slope (hp : 2 < C.p) {x₁ y₁ : Fe C} (hy : 2 * toF y₁ ≠ 0) :
    toF ((3 * x₁ * x₁ + Fin.ofNat C.p C.a) * inv (2 * y₁)) * (2 * toF y₁) =
      3 * toF x₁ ^ 2 + (C.a : ZMod C.p) := by
  rw [toF_mul, toF_inv hp, toF_mul, toF_ofNat' 2, inv_mul_cancel_right₀ hy, toF_add, toF_mul,
    toF_mul, toF_ofNat' 3, toF_ofNat, sq, mul_assoc]

theorem two_mul_ne_zero {y₁ : Fe C} (hy : y₁ ≠ -y₁) : 2 * toF y₁ ≠ 0 := by
  intro h
  apply hy
  apply toF_injective
  rw [toF_neg]
  linear_combination h

/-- The sum of two points of the curve is on the curve. -/
theorem onCurve_add (hp : 2 < C.p) {P Q : Point C} (hP : onCurve C P = true)
    (hQ : onCurve C Q = true) : onCurve C (add P Q) = true := by
  match P, Q with
  | .infinity, _ => exact hQ
  | .affine _ _, .infinity => exact hP
  | .affine x₁ y₁, .affine x₂ y₂ =>
    by_cases hc : x₁ = x₂ ∧ y₂ = -y₁
    · obtain ⟨rfl, rfl⟩ := hc
      rw [add_neg]; rfl
    by_cases hx : x₁ = x₂
    · subst hx
      obtain rfl : y₁ = y₂ := ((y_eq_or_eq_neg hP hQ).resolve_right (fun h => hc ⟨rfl, h⟩)).symm
      have hy : y₁ ≠ -y₁ := fun h => hc ⟨rfl, h⟩
      rw [add_tangent hy, onCurve_affine]
      rw [onCurve_affine] at hP
      have := tangent_on hP (two_mul_ne_zero hy) (toF_tangent_slope hp (two_mul_ne_zero hy))
      simp only [toF_sub, toF_mul, toF_ofNat' 2] at this ⊢
      exact this
    · rw [add_chord hx, onCurve_affine]
      rw [onCurve_affine] at hP hQ
      have := chord_on hP hQ (fun h => hx (toF_injective h)) (toF_chord_slope hp hx)
      simp only [toF_sub, toF_mul] at this ⊢
      exact this

/-! ## Representatives -/

theorem ZRep.smul {X Y Z c : ZMod C.p} {P : Point C} (hc : c ≠ 0) (h : ZRep C X Y Z P) :
    ZRep C (c * X) (c * Y) (c * Z) P := by
  cases P with
  | infinity =>
    obtain ⟨hX, hY, hZ⟩ := h
    exact ⟨by rw [hX, mul_zero], mul_ne_zero hc hY, by rw [hZ, mul_zero]⟩
  | affine x y =>
    obtain ⟨hZ, hX, hY⟩ := h
    exact ⟨mul_ne_zero hc hZ, by rw [hX]; ring, by rw [hY]; ring⟩

/-- On a curve with no point of order 2, `Y ≠ 0`. -/
theorem ZRep.y_ne_zero (hC : Good C) {X Y Z : ZMod C.p} {P : Point C}
    (hP : onCurve C P = true) (h : ZRep C X Y Z P) : Y ≠ 0 := by
  cases P with
  | infinity => exact h.2.1
  | affine x y =>
    obtain ⟨hZ, -, hY⟩ := h
    rw [hY]
    exact mul_ne_zero (Weierstrass.y_ne_zero hC.noTwoTorsion (onCurve_affine.mp hP)) hZ

theorem mul_pow_sub_two {Z : ZMod C.p} (hZ : Z ≠ 0) : Z * Z ^ (C.p - 2) = 1 := by
  have h2 := (Fact.out : C.p.Prime).two_le
  rw [← pow_succ', show C.p - 2 + 1 = C.p - 1 by omega_using [h2], ZMod.pow_card_sub_one_eq_one hZ]

/-- The affine `x` of a representative: `X / Z`, with the inverse by Fermat. -/
theorem ZRep.x_eq {X Y Z : ZMod C.p} {x y : Fe C} (h : ZRep C X Y Z (.affine x y)) :
    toF x = X * Z ^ (C.p - 2) := by
  obtain ⟨hZ, hX, -⟩ := h
  rw [hX, mul_assoc, mul_pow_sub_two hZ, mul_one]

theorem ZRep.y_eq {X Y Z : ZMod C.p} {x y : Fe C} (h : ZRep C X Y Z (.affine x y)) :
    toF y = Y * Z ^ (C.p - 2) := by
  obtain ⟨hZ, -, hY⟩ := h
  rw [hY, mul_assoc, mul_pow_sub_two hZ, mul_one]

end

/-! ## Completeness -/

theorem Good.onCurve_add (hC : Good C) {P Q : Point C} (hP : onCurve C P = true)
    (hQ : onCurve C Q = true) : onCurve C (add P Q) = true := by
  have : Fact C.p.Prime := ⟨hC.prime⟩
  exact Weierstrass.onCurve_add hC.two_lt hP hQ

/-- For points with `Z = 1`. -/
theorem rcbAdd_rep_one (hC : Good C) {x₁ y₁ x₂ y₂ : Fe C} (h1 : onCurve C (.affine x₁ y₁) = true)
    (h2 : onCurve C (.affine x₂ y₂) = true) :
    ZRep C (rcbAdd (C.a : ZMod C.p) (3 * (C.b : ZMod C.p)) (toF x₁) (toF y₁) 1 (toF x₂) (toF y₂) 1).1
      (rcbAdd (C.a : ZMod C.p) (3 * (C.b : ZMod C.p)) (toF x₁) (toF y₁) 1 (toF x₂) (toF y₂) 1).2.1
      (rcbAdd (C.a : ZMod C.p) (3 * (C.b : ZMod C.p)) (toF x₁) (toF y₁) 1 (toF x₂) (toF y₂) 1).2.2
      (add (.affine x₁ y₁) (.affine x₂ y₂)) := by
  have : Fact C.p.Prime := ⟨hC.prime⟩
  have hp := hC.two_lt
  have ht := hC.noTwoTorsion
  by_cases hc : x₁ = x₂ ∧ y₂ = -y₁
  · obtain ⟨rfl, rfl⟩ := hc
    rw [add_neg, toF_neg]
    exact rcbAdd_neg ht (two_ne_zero' hp) (onCurve_affine.mp h1)
  by_cases hx : x₁ = x₂
  · subst hx
    obtain rfl : y₁ = y₂ := ((y_eq_or_eq_neg h1 h2).resolve_right (fun h => hc ⟨rfl, h⟩)).symm
    have hy : y₁ ≠ -y₁ := fun h => hc ⟨rfl, h⟩
    rw [add_tangent hy]
    obtain ⟨hz, hX, hY⟩ := rcbAdd_tangent ht (two_ne_zero' hp) (onCurve_affine.mp h1)
      (toF_tangent_slope hp (two_mul_ne_zero hy))
    refine ⟨hz, ?_, ?_⟩
    · rw [hX]; simp only [toF_sub, toF_mul, toF_ofNat' 2]
    · rw [hY]; simp only [toF_sub, toF_mul, toF_ofNat' 2]
  · rw [add_chord hx]
    obtain ⟨hz, hX, hY⟩ := rcbAdd_chord ht (onCurve_affine.mp h1) (onCurve_affine.mp h2)
      (fun h => hx (toF_injective h)) (toF_chord_slope hp hx)
    refine ⟨hz, ?_, ?_⟩
    · rw [hX]; simp only [toF_sub, toF_mul]
    · rw [hY]; simp only [toF_sub, toF_mul]

/-- **Completeness**: on a curve with no point of order 2, `rcbAdd` maps
representatives of two points of the curve to a representative of their
sum. -/
theorem rcbAdd_rep (hC : Good C) {P Q : Point C} (hP : onCurve C P = true)
    (hQ : onCurve C Q = true) {X1 Y1 Z1 X2 Y2 Z2 X3 Y3 Z3 : ZMod C.p}
    (h1 : ZRep C X1 Y1 Z1 P) (h2 : ZRep C X2 Y2 Z2 Q)
    (h : rcbAdd (C.a : ZMod C.p) (3 * (C.b : ZMod C.p)) X1 Y1 Z1 X2 Y2 Z2 = (X3, Y3, Z3)) :
    ZRep C X3 Y3 Z3 (add P Q) := by
  have : Fact C.p.Prime := ⟨hC.prime⟩
  match P, Q with
  | .infinity, Q =>
    obtain ⟨rfl, hY1, rfl⟩ := h1
    rw [rcbAdd_zero_left, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact h2.smul (mul_ne_zero (pow_ne_zero 2 hY1) (h2.y_ne_zero hC hQ))
  | .affine x y, .infinity =>
    obtain ⟨rfl, hY2, rfl⟩ := h2
    rw [rcbAdd_comm, rcbAdd_zero_left, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact h1.smul (mul_ne_zero (pow_ne_zero 2 hY2) (h1.y_ne_zero hC hP))
  | .affine x₁ y₁, .affine x₂ y₂ =>
    obtain ⟨hZ1, rfl, rfl⟩ := h1
    obtain ⟨hZ2, rfl, rfl⟩ := h2
    rw [rcbAdd_scale, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (rcbAdd_rep_one hC hP hQ).smul
      (mul_ne_zero (pow_ne_zero 2 hZ1) (pow_ne_zero 2 hZ2))

/-! ## Over `Fin p` -/

theorem rep_iff {X Y Z : Fe C} {P : Point C} : Rep C X Y Z P ↔ ZRep C (toF X) (toF Y) (toF Z) P := by
  cases P with
  | infinity => simp only [Rep, ZRep, ← toF_zero (m := C.p), ne_eq, toF_inj]
  | affine x y => simp only [Rep, ZRep, ← toF_zero (m := C.p), ← toF_mul, ne_eq, toF_inj]

theorem toF_rcbAdd (a b3 X1 Y1 Z1 X2 Y2 Z2 : Fe C) :
    rcbAdd (toF a) (toF b3) (toF X1) (toF Y1) (toF Z1) (toF X2) (toF Y2) (toF Z2) =
      ((toF (rcbAdd a b3 X1 Y1 Z1 X2 Y2 Z2).1), toF (rcbAdd a b3 X1 Y1 Z1 X2 Y2 Z2).2.1,
        toF (rcbAdd a b3 X1 Y1 Z1 X2 Y2 Z2).2.2) := by
  simp only [rcbAdd, toF_add, toF_mul, toF_sub]

/-- The curve's coefficients in `Fin p`. -/
theorem toF_ab (C : Curve) : toF (Fin.ofNat C.p C.a) = (C.a : ZMod C.p) ∧
    toF (Fin.ofNat C.p (3 * C.b)) = 3 * (C.b : ZMod C.p) := by
  rw [toF_ofNat, toF_ofNat, Nat.cast_mul, Nat.cast_ofNat]
  exact ⟨rfl, rfl⟩

/-- **Completeness**, over `Fin p`. -/
theorem Good.rep_add (hC : Good C) {P Q : Point C} (hP : onCurve C P = true)
    (hQ : onCurve C Q = true) {X1 Y1 Z1 X2 Y2 Z2 X3 Y3 Z3 : Fe C}
    (h1 : Rep C X1 Y1 Z1 P) (h2 : Rep C X2 Y2 Z2 Q)
    (h : rcbAdd (Fin.ofNat C.p C.a) (Fin.ofNat C.p (3 * C.b)) X1 Y1 Z1 X2 Y2 Z2 = (X3, Y3, Z3)) :
    Rep C X3 Y3 Z3 (Spec.Weierstrass.add P Q) := by
  rw [rep_iff] at h1 h2 ⊢
  refine rcbAdd_rep hC hP hQ h1 h2 ?_
  rw [← (toF_ab C).1, ← (toF_ab C).2, toF_rcbAdd, h]

theorem Good.one_ne_zero_fe (hC : Good C) : (1 : Fe C) ≠ 0 := by
  have : Fact C.p.Prime := ⟨hC.prime⟩
  intro h
  have := congrArg toF h
  rw [toF_one, toF_zero] at this
  exact one_ne_zero this

/-- The affine `x` of a representative: `X / Z`, with the inverse by Fermat. -/
theorem Good.rep_x_eq (hC : Good C) {X Y Z : Fe C} {x y : Fe C} (h : Rep C X Y Z (.affine x y)) :
    x = X * Z ^ (C.p - 2) := by
  have : Fact C.p.Prime := ⟨hC.prime⟩
  rw [← toF_inj, toF_mul, toF_npow]
  exact (rep_iff.mp h).x_eq

theorem Good.rep_y_eq (hC : Good C) {X Y Z : Fe C} {x y : Fe C} (h : Rep C X Y Z (.affine x y)) :
    y = Y * Z ^ (C.p - 2) := by
  have : Fact C.p.Prime := ⟨hC.prime⟩
  rw [← toF_inj, toF_mul, toF_npow]
  exact (rep_iff.mp h).y_eq

end VG.Proof.Weierstrass
