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
coordinates are `X / Z` and `Y / Z`, with the inverse by Fermat. Its proof,
`Good.law` (`LadderStep.lean`), is in `ZMod C.p` with Mathlib's algebra and
elliptic curves, which only a curve's own facts (e.g. `Proof/P256/Curve.lean`)
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

/-- What the proofs of the code need of the group law of `C`. -/
structure Law (C : Curve) : Prop where
  one_ne_zero : (1 : Fe C) ≠ 0
  /-- The complete formulas compute the sum. -/
  add : ∀ {P Q : Point C}, onCurve C P = true → onCurve C Q = true →
    ∀ {X1 Y1 Z1 X2 Y2 Z2 X3 Y3 Z3 : Fe C}, Rep C X1 Y1 Z1 P → Rep C X2 Y2 Z2 Q →
      rcbAddC C X1 Y1 Z1 X2 Y2 Z2 = (X3, Y3, Z3) → Rep C X3 Y3 Z3 (Spec.Weierstrass.add P Q)
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
