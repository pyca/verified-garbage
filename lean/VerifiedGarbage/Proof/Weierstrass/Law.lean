import VerifiedGarbage.Proof.Weierstrass.Rcb
import VerifiedGarbage.Spec.Weierstrass

/-!
# The group law, as the proofs of the code use it

`Rep C X Y Z P`: the projective triple `(X : Y : Z)` over `Fin C.p`, the
specification's field, represents the point `P` of the specification (`O` is
`(0 : Y : 0)` with `Y ≠ 0`, `(x, y)` is `(xZ : yZ : Z)` with `Z ≠ 0`).

`Law C` is what the proofs of the code need of the curve `C`'s group law:
the complete addition `rcbAdd` maps representatives of two points of the
curve to a representative of their sum (`add`), and so an iteration of the
ladder keeps a representative of `[k >>> j]P` (`step`); multiples of a
point of the curve are on the curve; and a representative's affine
coordinates are `X / Z` and `Y / Z`, with the inverse by Fermat; and the
points of the curve form an abelian group (`GroupRep`, in Lean's core
`IntModule`), so sums of points may be rearranged; and the checks of a
comb's tables without inverses (`chordOk`, `tangentOk`) give sums. Its proof, `Good.law`
(`Group.lean`), is in `ZMod C.p` with Mathlib's algebra and elliptic curves, which only a curve's own facts (e.g. `Proof/P256/Curve.lean`)
import: the proofs of the code take `Law C` as a hypothesis, and only the
registration files supply it, so none of them loads that algebra.
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

/-- `(X : Y : Z)` represents `P`. -/
def Rep (C : Curve) (X Y Z : Fe C) : Point C → Prop
  | .infinity => X = 0 ∧ Y ≠ 0 ∧ Z = 0
  | .affine x y => Z ≠ 0 ∧ X = x * Z ∧ Y = y * Z

/-- The curve's coefficients `a` and `3b` in `Fin p`, as the complete
addition takes them. -/
abbrev rcbAddC (C : Curve) (X1 Y1 Z1 X2 Y2 Z2 : Fe C) : Fe C × Fe C × Fe C :=
  rcbAdd (Fin.ofNat C.p C.a) (Fin.ofNat C.p (3 * C.b)) X1 Y1 Z1 X2 Y2 Z2

/-- The reflection `(x, -y)` of a point, and `O`'s. -/
def negPt {C : Curve} : Point C → Point C
  | .infinity => .infinity
  | .affine x y => .affine x (-y)

/-- The group law in an abelian group (a module over `Int`, in Lean's core): a
map from the points of the curve to it, additive, injective, taking multiples
to multiples and the reflection to the negation. -/
structure GroupRep (C : Curve) (A : Type) [Lean.Grind.IntModule A] (f : Point C → A) : Prop where
  add : ∀ {P Q : Point C}, onCurve C P = true → onCurve C Q = true → f (add P Q) = f P + f Q
  mul : ∀ {P : Point C}, onCurve C P = true → ∀ k : Nat, f (mul k P) = (k : Int) • f P
  neg : ∀ {P : Point C}, onCurve C P = true → f (negPt P) = -f P
  inj : ∀ {P Q : Point C}, onCurve C P = true → onCurve C Q = true → f P = f Q → P = Q

/-- An affine point with `Nat` coordinates. -/
def ptN (C : Curve) (q : Nat × Nat) : Point C := .affine (Fin.ofNat C.p q.1) (Fin.ofNat C.p q.2)

/-- `(x₃, y₃) = (x₁, y₁) + (x₂, y₂)` by the chord, for `x₁ ≠ x₂`, checked
without inverses: `(x₃ + x₁ + x₂)(x₂ - x₁)² = (y₂ - y₁)²` and
`(y₃ + y₁)(x₂ - x₁) = (y₂ - y₁)(x₁ - x₃)`, modulo `p`. -/
def chordOk (p : Nat) (x1 y1 x2 y2 x3 y3 : Nat) : Bool :=
  x1 != x2 &&
  (x3 + x1 + x2) * ((x2 + p - x1) * (x2 + p - x1)) % p == (y2 + p - y1) * (y2 + p - y1) % p &&
  (y3 + y1) * (x2 + p - x1) % p == (y2 + p - y1) * (x1 + p - x3) % p

/-- `(x₃, y₃) = 2 (x₁, y₁)` by the tangent, for `2 y₁ ≠ 0`, checked without
inverses: `(x₃ + 2x₁)(2y₁)² = (3x₁² + a)²` and
`(y₃ + y₁)(2y₁) = (3x₁² + a)(x₁ - x₃)`, modulo `p`. -/
def tangentOk (p a : Nat) (x1 y1 x3 y3 : Nat) : Bool :=
  2 * y1 % p != 0 &&
  (x3 + 2 * x1) * (2 * y1 * (2 * y1)) % p == (3 * x1 * x1 + a) * (3 * x1 * x1 + a) % p &&
  (y3 + y1) * (2 * y1) % p == (3 * x1 * x1 + a) * (x1 + p - x3) % p

/-- What the proofs of the code need of the group law of `C`. -/
structure Law (C : Curve) : Prop where
  one_ne_zero : (1 : Fe C) ≠ 0
  /-- `Fin p` has no zero divisors (`p` is prime). -/
  mul_ne_zero : ∀ {a b : Fe C}, a ≠ 0 → b ≠ 0 → a * b ≠ 0
  /-- The complete formulas compute the sum. -/
  add : ∀ {P Q : Point C}, onCurve C P = true → onCurve C Q = true →
    ∀ {X1 Y1 Z1 X2 Y2 Z2 X3 Y3 Z3 : Fe C}, Rep C X1 Y1 Z1 P → Rep C X2 Y2 Z2 Q →
      rcbAddC C X1 Y1 Z1 X2 Y2 Z2 = (X3, Y3, Z3) → Rep C X3 Y3 Z3 (Spec.Weierstrass.add P Q)
  /-- Sums of points of the curve are on the curve. -/
  onCurve_add : ∀ {P Q : Point C}, onCurve C P = true → onCurve C Q = true →
    onCurve C (Spec.Weierstrass.add P Q) = true
  /-- Multiples of a point of the curve are on the curve. -/
  onCurve_mul : ∀ {P : Point C}, onCurve C P = true → ∀ k, onCurve C (mul k P) = true
  /-- An iteration of the ladder: from a representative of `[k >>> (j + 1)]P`,
  the double `D` and `T = D + P`, and `T` if bit `j` of `k` is set, else `D`,
  represents `[k >>> j]P`. -/
  step : ∀ {P : Point C}, onCurve C P = true → ∀ {k j : Nat} {Px Py Pz X Y Z X2 Y2 Z2 X3 Y3 Z3 : Fe C},
    Rep C Px Py Pz P → Rep C X Y Z (mul (k >>> (j + 1)) P) →
    rcbAddC C X Y Z X Y Z = (X2, Y2, Z2) → rcbAddC C X2 Y2 Z2 Px Py Pz = (X3, Y3, Z3) →
    Rep C (if k.testBit j then X3 else X2) (if k.testBit j then Y3 else Y2)
      (if k.testBit j then Z3 else Z2) (mul (k >>> j) P)
  /-- The affine `x` of a representative: `X / Z`, with the inverse by Fermat. -/
  x_eq : ∀ {X Y Z x y : Fe C}, Rep C X Y Z (.affine x y) → x = X * Z ^ (C.p - 2)
  y_eq : ∀ {X Y Z x y : Fe C}, Rep C X Y Z (.affine x y) → y = Y * Z ^ (C.p - 2)
  /-- The points of the curve form an abelian group, the specification's
  addition its addition (`GroupRep`). -/
  group : ∃ (A : Type) (_ : Lean.Grind.IntModule A) (f : Point C → A), GroupRep C A f
  /-- A chord checked without inverses (`chordOk`) gives the sum of two
  points of distinct `x`. -/
  chord : ∀ {x1 y1 x2 y2 x3 y3 : Nat}, x1 < C.p → x2 < C.p → y1 < C.p → x3 < C.p →
    chordOk C.p x1 y1 x2 y2 x3 y3 = true →
    Spec.Weierstrass.add (ptN C (x1, y1)) (ptN C (x2, y2)) = ptN C (x3, y3)
  /-- A tangent checked without inverses (`tangentOk`) gives the double. -/
  tangent : ∀ {x1 y1 x3 y3 : Nat}, x3 < C.p → tangentOk C.p C.a x1 y1 x3 y3 = true →
    Spec.Weierstrass.add (ptN C (x1, y1)) (ptN C (x1, y1)) = ptN C (x3, y3)

variable {C : Curve}

theorem one_ne_zero_fe (hC : Law C) : (1 : Fe C) ≠ 0 := hC.one_ne_zero

theorem rep_infinity' (hC : Law C) : Rep C 0 1 0 .infinity := ⟨rfl, hC.one_ne_zero, rfl⟩

theorem rep_affine' (hC : Law C) (x y : Fe C) : Rep C x y 1 (.affine x y) :=
  ⟨hC.one_ne_zero, (Lean.Grind.Semiring.mul_one _).symm, (Lean.Grind.Semiring.mul_one _).symm⟩

/-- **Completeness**, over `Fin p`. -/
theorem Rep.add (hC : Law C) {P Q : Point C} (hP : onCurve C P = true)
    (hQ : onCurve C Q = true) {X1 Y1 Z1 X2 Y2 Z2 X3 Y3 Z3 : Fe C}
    (h1 : Rep C X1 Y1 Z1 P) (h2 : Rep C X2 Y2 Z2 Q)
    (h : rcbAdd (Fin.ofNat C.p C.a) (Fin.ofNat C.p (3 * C.b)) X1 Y1 Z1 X2 Y2 Z2 = (X3, Y3, Z3)) :
    Rep C X3 Y3 Z3 (Spec.Weierstrass.add P Q) :=
  hC.add hP hQ h1 h2 h

theorem ladder_step (hC : Law C) {P : Point C} (hP : onCurve C P = true) {k j : Nat}
    {Px Py Pz X Y Z X2 Y2 Z2 X3 Y3 Z3 : Fe C}
    (hPr : Rep C Px Py Pz P) (hR : Rep C X Y Z (mul (k >>> (j + 1)) P))
    (h2 : rcbAdd (Fin.ofNat C.p C.a) (Fin.ofNat C.p (3 * C.b)) X Y Z X Y Z = (X2, Y2, Z2))
    (h3 : rcbAdd (Fin.ofNat C.p C.a) (Fin.ofNat C.p (3 * C.b)) X2 Y2 Z2 Px Py Pz = (X3, Y3, Z3)) :
    Rep C (if k.testBit j then X3 else X2) (if k.testBit j then Y3 else Y2)
      (if k.testBit j then Z3 else Z2) (mul (k >>> j) P) :=
  hC.step hP hPr hR h2 h3

theorem Rep.z_eq_zero_iff {X Y Z : Fe C} {P : Point C} (h : Rep C X Y Z P) :
    Z = 0 ↔ P = .infinity := by
  cases P with
  | infinity => exact ⟨fun _ => rfl, fun _ => h.2.2⟩
  | affine x y => exact ⟨fun h0 => absurd h0 h.1, fun h' => nomatch h'⟩

/-- The affine `x` of a representative: `X / Z`, with the inverse by Fermat. -/
theorem Rep.x_eq (hC : Law C) {X Y Z : Fe C} {x y : Fe C} (h : Rep C X Y Z (.affine x y)) :
    x = X * Z ^ (C.p - 2) := hC.x_eq h

theorem Rep.y_eq (hC : Law C) {X Y Z : Fe C} {x y : Fe C} (h : Rep C X Y Z (.affine x y)) :
    y = Y * Z ^ (C.p - 2) := hC.y_eq h

theorem Rep.infinity_x {X Y Z : Fe C} (h : Rep C X Y Z .infinity) : X * Z ^ (C.p - 2) = 0 := by
  rw [h.1]
  exact Lean.Grind.Semiring.zero_mul _

/-- `(x * x) ^ k` is `x ^ (2 k)`. -/
theorem sq_pow {m : Nat} [NeZero m] (x : Fin m) (k : Nat) : (x * x) ^ k = x ^ (k + k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Lean.Grind.Semiring.pow_succ, ih, show k + 1 + (k + 1) = (k + k) + 1 + 1 by omega,
      Lean.Grind.Semiring.pow_succ, Lean.Grind.Semiring.pow_succ, Lean.Grind.Semiring.mul_assoc]

/-- The specification's `pow` is the power. -/
theorem pow_eq_npow {m : Nat} [NeZero m] (x : Fin m) (e : Nat) : pow x e = x ^ e := by
  induction e using Nat.strongRecOn generalizing x with
  | _ e ih =>
    rw [pow]
    by_cases h0 : e = 0
    · subst h0; rfl
    · simp only [h0, ite_false]
      rw [ih (e / 2) (by omega), sq_pow]
      by_cases h2 : e % 2 = 0
      · simp only [h2, ite_true]
        exact congrArg (x ^ ·) (by omega)
      · simp only [h2, ite_false]
        rw [show x ^ e = x ^ (e / 2 + e / 2 + 1) from congrArg (x ^ ·) (by omega),
          Lean.Grind.Semiring.pow_succ, Lean.Grind.CommSemiring.mul_comm]

end VG.Proof.Weierstrass
