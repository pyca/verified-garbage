import VerifiedGarbage.Proof.Weierstrass.Jac

/-!
# Mixed Jacobian addition

`maddJF` adds an affine point `(x₂, y₂)` to a Jacobian `(X₁ : Y₁ : Z₁)`
(madd-2004-hmv: 8 products and 3 squares): with `H = x₂Z₁² - X₁` and
`r = y₂Z₁³ - Y₁`, `X₃ = r² - H³ - 2X₁H²`, `Y₃ = r(X₁H² - X₃) - Y₁H³`,
`Z₃ = Z₁H`. It fails when the two points are equal (`H = r = 0`), and only
then: for points of the curve its projective triple `(X₃Z₃ : Y₃ : Z₃³)` is
proportional to Algorithm 5's sum of the projective triples (`maddJF_cross`),
which is a representative by `Law.add3m`; when the points have the same `x`
and are not equal, `Z₃ = 0` and their sum is `O` (`InvJ.madd`).
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass VG.Impl.Weierstrass

section
variable {F : Type _} [Lean.Grind.CommRing F]

/-- Mixed Jacobian addition, in the code's order. -/
def maddJF (X1 Y1 Z1 x2 y2 : F) : F × F × F :=
  let t0 := Z1 * Z1; let t1 := x2 * t0; let t2 := Z1 * t0; let t2 := y2 * t2
  let t1 := t1 - X1; let t2 := t2 - Y1; let t3 := t1 * t1; let t4 := t1 * t3
  let t3 := X1 * t3; let ox := t2 * t2; let ox := ox - t4; let t5 := t3 + t3; let ox := ox - t5
  let t3 := t3 - ox; let t3 := t2 * t3; let t4 := Y1 * t4; let oy := t3 - t4
  let oz := Z1 * t1
  (ox, oy, oz)

theorem maddJF_z (X1 Y1 Z1 x2 y2 : F) : (maddJF X1 Y1 Z1 x2 y2).2.2 = Z1 * (x2 * (Z1 * Z1) - X1) := by
  simp only [maddJF]

/-- For points of the curve, the projective triple of the Jacobian sum is
proportional to Algorithm 5's sum. -/
theorem maddJF_cross (b x1 y1 Z x2 y2 : F) (e1 : y1 * y1 = x1 * x1 * x1 + -3 * x1 + b)
    (e2 : y2 * y2 = x2 * x2 * x2 + -3 * x2 + b) :
    (rcbAdd3m b (x1 * (Z * Z) * Z) (y1 * (Z * Z * Z)) (Z * Z * Z) x2 y2).1 *
        ((maddJF (x1 * (Z * Z)) (y1 * (Z * Z * Z)) Z x2 y2).2.2 *
          (maddJF (x1 * (Z * Z)) (y1 * (Z * Z * Z)) Z x2 y2).2.2 *
          (maddJF (x1 * (Z * Z)) (y1 * (Z * Z * Z)) Z x2 y2).2.2) =
      (rcbAdd3m b (x1 * (Z * Z) * Z) (y1 * (Z * Z * Z)) (Z * Z * Z) x2 y2).2.2 *
        ((maddJF (x1 * (Z * Z)) (y1 * (Z * Z * Z)) Z x2 y2).1 *
          (maddJF (x1 * (Z * Z)) (y1 * (Z * Z * Z)) Z x2 y2).2.2) ∧
    (rcbAdd3m b (x1 * (Z * Z) * Z) (y1 * (Z * Z * Z)) (Z * Z * Z) x2 y2).2.1 *
        ((maddJF (x1 * (Z * Z)) (y1 * (Z * Z * Z)) Z x2 y2).2.2 *
          (maddJF (x1 * (Z * Z)) (y1 * (Z * Z * Z)) Z x2 y2).2.2 *
          (maddJF (x1 * (Z * Z)) (y1 * (Z * Z * Z)) Z x2 y2).2.2) =
      (rcbAdd3m b (x1 * (Z * Z) * Z) (y1 * (Z * Z * Z)) (Z * Z * Z) x2 y2).2.2 *
        (maddJF (x1 * (Z * Z)) (y1 * (Z * Z * Z)) Z x2 y2).2.1 := by
  simp only [maddJF, rcbAdd3m]
  constructor <;> grind

end

/-- `maddJ` on the slots `0, 1, …` (the code's `Impl.Weierstrass.maddJ`). -/
def maddJN : List FOp := maddJ ⟨9, 10, 0, 1, 2, 3, 4, 5⟩ ⟨11, 12, 13⟩ ⟨14, 15, 16⟩ ⟨6, 7, 8⟩

theorem maddJN_ok : NumOk maddJN := ⟨by decide, by decide, by decide⟩

theorem maddJ_eq (S : RcbSlots) (p q o : Pt) : maddJ S p q o = ofN maddJN S p q o := rfl

theorem maddJN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    (runOps maddJN e 6, runOps maddJN e 7, runOps maddJN e 8) =
      maddJF (e 11) (e 12) (e 13) (e 14) (e 15) := rfl

variable {C : Curve}

theorem Law.cancel (hC : Law C) {a c d : Fe C} (ha : a ≠ 0) (h : a * c = a * d) : c = d :=
  Classical.byContradiction fun hne =>
    hC.mul_ne_zero ha (show c - d ≠ 0 from fun h0 => hne (by grind)) (by grind)

/-- Mixed addition keeps `InvJ`, for a Jacobian triple of a point other than
`O` (`Z₁ ≠ 0`) and an affine point of the curve other than it. -/
theorem InvJ.madd (hC : Law C) (ha : AM3 C) {X1 Y1 Z1 x2 y2 : Fe C} {Q : Point C}
    (hQ : onCurve C Q = true) (hE : onCurve C (.affine x2 y2) = true)
    (h : InvJ C X1 Y1 Z1 Q) (hZ : Z1 ≠ 0) (hne : Q ≠ .affine x2 y2) :
    InvJ C (maddJF X1 Y1 Z1 x2 y2).1 (maddJF X1 Y1 Z1 x2 y2).2.1 (maddJF X1 Y1 Z1 x2 y2).2.2
      (Spec.Weierstrass.add Q (.affine x2 y2)) := by
  rcases h with ⟨-, hZ0⟩ | h
  · exact absurd hZ0 hZ
  cases Q with
  | infinity => exact absurd h.2.2 (cube_ne_zero hC hZ)
  | affine x1 y1 =>
    obtain ⟨hZ3, hXZ, hY⟩ := h
    have hX : X1 = x1 * (Z1 * Z1) := hC.cancel hZ (by grind)
    subst hX hY
    have e1 : y1 * y1 = x1 * x1 * x1 + -3 * x1 + Fin.ofNat C.p C.b := by
      have h1 := hQ; simp only [onCurve, decide_eq_true_eq] at h1; rw [ha] at h1; exact h1
    have e2 : y2 * y2 = x2 * x2 * x2 + -3 * x2 + Fin.ofNat C.p C.b := by
      have h2 := hE; simp only [onCurve, decide_eq_true_eq] at h2; rw [ha] at h2; exact h2
    by_cases hx : x1 = x2
    · -- The same `x`: `y₂ = -y₁` (the points differ), the sum is `O`, and `Z₃ = 0`.
      subst hx
      have hy : y2 = -y1 := by
        have hyy : (y2 - y1) * (y2 + y1) = 0 := by grind
        refine Classical.byContradiction fun hy => ?_
        have h1 : y2 - y1 ≠ 0 := fun h0 => hne (by congr 1; grind)
        exact hC.mul_ne_zero h1 (fun h0 => hy (by grind)) hyy
      refine Or.inl ⟨?_, ?_⟩
      · simp only [Spec.Weierstrass.add, hy, and_self, ↓reduceIte]
      · rw [maddJF_z]; grind
    · -- Distinct `x`: Algorithm 5's sum is a representative, and proportional.
      obtain ⟨cx, cy⟩ := maddJF_cross (Fin.ofNat C.p C.b) x1 y1 Z1 x2 y2 e1 e2
      have hH : x2 * (Z1 * Z1) - x1 * (Z1 * Z1) ≠ 0 := by
        intro h0
        have : (x2 - x1) * (Z1 * Z1) = 0 := by grind
        exact hC.mul_ne_zero (fun h1 => hx (by grind)) (hC.mul_ne_zero hZ hZ) this
      have hZ3' : (maddJF (x1 * (Z1 * Z1)) (y1 * (Z1 * Z1 * Z1)) Z1 x2 y2).2.2 ≠ 0 := by
        rw [maddJF_z]; exact hC.mul_ne_zero hZ hH
      generalize maddJF (x1 * (Z1 * Z1)) (y1 * (Z1 * Z1 * Z1)) Z1 x2 y2 = M at cx cy hZ3' ⊢
      generalize hRv : rcbAdd3m (Fin.ofNat C.p C.b) (x1 * (Z1 * Z1) * Z1) (y1 * (Z1 * Z1 * Z1))
        (Z1 * Z1 * Z1) x2 y2 = R at cx cy
      have hR := hC.add3m ha hQ hE (X1 := x1 * (Z1 * Z1) * Z1) (Y1 := y1 * (Z1 * Z1 * Z1))
        (Z1 := Z1 * Z1 * Z1) (X2 := x2) (Y2 := y2) (X3 := R.1) (Y3 := R.2.1) (Z3 := R.2.2)
        ⟨hZ3, Lean.Grind.Semiring.mul_assoc _ _ _, rfl⟩
        ⟨hC.one_ne_zero, (Lean.Grind.Semiring.mul_one _).symm, (Lean.Grind.Semiring.mul_one _).symm⟩
        (by rw [hRv])
      generalize hS : Spec.Weierstrass.add (Point.affine x1 y1) (Point.affine x2 y2) = S at hR ⊢
      cases S with
      | infinity =>
        have : Spec.Weierstrass.add (Point.affine x1 y1) (Point.affine x2 y2) ≠ .infinity := by
          simp only [Spec.Weierstrass.add, hx, false_and, ↓reduceIte, ne_eq, not_false_eq_true]
          exact fun h => nomatch h
        exact absurd hS this
      | affine x3 y3 =>
        obtain ⟨hRZ, hRX, hRY⟩ := hR
        refine Or.inr ⟨cube_ne_zero hC hZ3', ?_, ?_⟩
        · refine hC.cancel hRZ ?_
          rw [← cx, hRX]; grind
        · refine hC.cancel hRZ ?_
          rw [← cy, hRY]; grind

theorem infinity_add' (P : Point C) : Spec.Weierstrass.add .infinity P = P := by
  cases P <;> rfl

/-- A representative with `Z = 1` is the affine point. -/
theorem Rep.eq_affine (hC : Law C) {x y : Fe C} {Q : Point C} (h : Rep C x y 1 Q) : Q = .affine x y := by
  cases Q with
  | infinity => exact absurd h.2.2 hC.one_ne_zero
  | affine x' y' =>
    obtain ⟨-, hx, hy⟩ := h
    rw [Lean.Grind.Semiring.mul_one] at hx hy
    rw [hx, hy]

/-- A representative with `Z = 1` or `Z = 0` (`O`) is a Jacobian triple. -/
theorem InvJ.of_rep01 {X Y Z : Fe C} {Q : Point C} (h : Rep C X Y Z Q) (hz : Z = 1 ∨ Z = 0) :
    InvJ C X Y Z Q := by
  rcases hz with rfl | rfl
  · refine Or.inr ?_
    rw [Lean.Grind.Semiring.mul_one, Lean.Grind.Semiring.mul_one, Lean.Grind.Semiring.mul_one]
    exact h
  · cases Q with
    | infinity => exact Or.inl ⟨rfl, rfl⟩
    | affine => exact absurd rfl h.1

/-- A Jacobian triple with `Z = 0` is of `O`. -/
theorem InvJ.eq_infinity {X Y : Fe C} {Q : Point C} (h : InvJ C X Y 0 Q) : Q = .infinity := by
  rcases h with ⟨hQ, -⟩ | h
  · exact hQ
  · cases Q with
    | infinity => rfl
    | affine => exact absurd (by grind) h.1

end VG.Proof.Weierstrass
