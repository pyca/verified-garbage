import VerifiedGarbage.Proof.Weierstrass.Law3

/-!
# Doublings in Jacobian coordinates, for `a = -3`

A Jacobian triple `(X : Y : Z)` stands for the projective `(XZ : Y : Z³)`
(affine `(X / Z², Y / Z³)`). Doubling it (`dblJF`, dbl-2001-b: 3 products and
5 squares) is, for a point of the curve (`Y² = X³ - 3XZ⁴ + bZ⁶`), Algorithm 6
on the projective triple (`dblJF_conv`), so it doubles by `Law.dbl3`.

`InvJ C X Y Z Q`: the triple stands for `Q`, or `Q` is `O` and `Z = 0` (the
Jacobian triple of `O` from a projective `(0 : Y : 0)` is zero). A projective
representative gives one (`InvJ.of_rep`), doubling keeps it (`InvJ.dbl`), and
back in projective coordinates, with `Y = 1` where `Z = 0`, it is a
representative again (`InvJ.out`).
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

section
variable {F : Type _} [Lean.Grind.CommRing F]

/-- Jacobian doubling for `a = -3`, in the code's order. -/
def dblJF (X Y Z : F) : F × F × F :=
  let delta := Z * Z; let gamma := Y * Y; let beta := X * gamma
  let t3 := X - delta; let ox := X + delta; let t3 := t3 * ox; let ox := t3 + t3; let t3 := ox + t3
  let t2 := beta + beta; let t2 := t2 + t2
  let oz := Y + Z; let oz := oz * oz; let oz := oz - gamma; let oz := oz - delta
  let ox := t3 * t3; let ox := ox - t2; let ox := ox - t2
  let oy := t2 - ox; let oy := t3 * oy
  let t1 := gamma * gamma; let t1 := t1 + t1; let t1 := t1 + t1; let t1 := t1 + t1
  let oy := oy - t1
  (ox, oy, oz)

/-- Jacobian doubling is Algorithm 6 on the projective triple, on the curve. -/
theorem dblJF_conv (b X Y Z : F)
    (hE : Y * Y = X * X * X - 3 * X * Z * Z * Z * Z + b * Z * Z * Z * Z * Z * Z) :
    ((dblJF X Y Z).1 * (dblJF X Y Z).2.2, (dblJF X Y Z).2.1,
      (dblJF X Y Z).2.2 * (dblJF X Y Z).2.2 * (dblJF X Y Z).2.2) = rcbDbl3 b (X * Z) Y (Z * Z * Z) := by
  simp only [dblJF, rcbDbl3, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> grind

theorem dblJF_z (X Y Z : F) : (dblJF X Y Z).2.2 = 2 * Y * Z := by
  simp only [dblJF]; grind

end

variable {C : Curve}

/-- The Jacobian triple stands for `Q`, or `Q` is `O` with `Z = 0`. -/
def InvJ (C : Curve) (X Y Z : Fe C) (Q : Point C) : Prop :=
  (Q = .infinity ∧ Z = 0) ∨ Rep C (X * Z) Y (Z * Z * Z) Q

theorem cube_ne_zero (hC : Law C) {Z : Fe C} (h : Z ≠ 0) : Z * Z * Z ≠ 0 :=
  hC.mul_ne_zero (hC.mul_ne_zero h h) h

/-- From a projective representative: `(XZ : YZ² : Z)`. -/
theorem InvJ.of_rep (hC : Law C) {X Y Z : Fe C} {Q : Point C} (h : Rep C X Y Z Q) :
    InvJ C (X * Z) (Y * (Z * Z)) Z Q := by
  cases Q with
  | infinity => exact Or.inl ⟨rfl, h.2.2⟩
  | affine x y =>
    obtain ⟨hZ, hX, hY⟩ := h
    refine Or.inr ⟨cube_ne_zero hC hZ, ?_, ?_⟩
    · rw [hX]; grind
    · rw [hY]; grind

theorem add_infinity_infinity : Spec.Weierstrass.add (.infinity : Point C) .infinity = .infinity := rfl

/-- A doubling keeps it. -/
theorem InvJ.dbl (hC : Law C) (ha : AM3 C) {X Y Z : Fe C} {Q : Point C} (hQ : onCurve C Q = true)
    (h : InvJ C X Y Z Q) :
    InvJ C (dblJF X Y Z).1 (dblJF X Y Z).2.1 (dblJF X Y Z).2.2 (Spec.Weierstrass.add Q Q) := by
  rcases h with ⟨rfl, hZ⟩ | h
  · refine Or.inl ⟨add_infinity_infinity, ?_⟩
    rw [dblJF_z, hZ]; grind
  · cases Q with
    | infinity =>
      obtain ⟨-, -, hZ3⟩ := h
      have hZ : Z = 0 := by
        by_contra hZ
        exact cube_ne_zero hC hZ hZ3
      refine Or.inl ⟨add_infinity_infinity, ?_⟩
      rw [dblJF_z, hZ]; grind
    | affine x y =>
      obtain ⟨hZ3, hXZ, hY⟩ := h
      have hZ : Z ≠ 0 := fun h0 => hZ3 (by rw [h0]; grind)
      -- `X = x Z²`, cancelling `Z`.
      have hX : X = x * (Z * Z) := by
        by_contra hne
        have h1 : X - x * (Z * Z) ≠ 0 := fun h0 => hne (by grind)
        exact hC.mul_ne_zero h1 hZ (by grind)
      have hC' := hQ
      simp only [onCurve, decide_eq_true_eq] at hC'
      rw [ha] at hC'
      have hE : Y * Y = X * X * X - 3 * X * Z * Z * Z * Z + Fin.ofNat C.p C.b * Z * Z * Z * Z * Z * Z := by
        rw [hX, hY]
        have : y * y * (Z * Z * Z * Z * Z * Z) = (x * x * x + -3 * x + Fin.ofNat C.p C.b) *
            (Z * Z * Z * Z * Z * Z) := by rw [hC']
        grind
      refine Or.inr (hC.dbl3 ha hQ (⟨hZ3, hXZ, hY⟩ : Rep C (X * Z) Y (Z * Z * Z) (.affine x y)) ?_)
      exact (dblJF_conv _ X Y Z hE).symm

/-- `InvJ.of_rep`, for the values `toJ` computes (`z` zero). -/
theorem InvJ.of_toJ (hC : Law C) {X Y Z z X' Y' Z' : Fe C} {Q : Point C} (h : Rep C X Y Z Q)
    (hz : z = 0) (hv : (X', Y', Z') = (X * Z, Y * (Z * Z), Z + z)) : InvJ C X' Y' Z' Q := by
  simp only [Prod.mk.injEq] at hv
  obtain ⟨rfl, rfl, rfl⟩ := hv
  rw [hz, show Z + 0 = Z by grind]
  exact InvJ.of_rep hC h

/-- `InvJ.dbl`, for the values a doubling computes. -/
theorem InvJ.dbl' (hC : Law C) (ha : AM3 C) {X Y Z X' Y' Z' : Fe C} {Q : Point C}
    (hQ : onCurve C Q = true) (h : InvJ C X Y Z Q) (hv : (X', Y', Z') = dblJF X Y Z) :
    InvJ C X' Y' Z' (Spec.Weierstrass.add Q Q) := by
  have h' := InvJ.dbl hC ha hQ h
  rw [← hv] at h'
  exact h'

/-- Back in projective coordinates, with `Y = 1` where `Z = 0`: a representative. -/
theorem InvJ.out (hC : Law C) {X Y Z : Fe C} {Q : Point C} (h : InvJ C X Y Z Q) :
    Rep C (X * Z) (if Z = 0 then 1 else Y) (Z * Z * Z) Q := by
  by_cases hZ : Z = 0
  · rw [ite_eq_left_iff.mpr (fun h => absurd hZ h), hZ]
    have hQ : Q = .infinity := by
      rcases h with ⟨hQ, -⟩ | h
      · exact hQ
      · cases Q with
        | infinity => rfl
        | affine x y => exact absurd (by rw [hZ]; grind) h.1
    subst hQ
    exact ⟨by grind, hC.one_ne_zero, by grind⟩
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hZ)]
    rcases h with ⟨-, h0⟩ | h
    · exact absurd h0 hZ
    · exact h


/-! ## The programs on numbered slots -/

open VG.Impl.Weierstrass in
/-- Jacobian doubling on numbered slots (`p` at `11 … 13`, `o` at `6 … 8`). -/
def dblJN : List FOp := dblJ ⟨9, 10, 0, 1, 2, 3, 4, 5⟩ ⟨11, 12, 13⟩ ⟨6, 7, 8⟩

open VG.Impl.Weierstrass in
/-- To Jacobian coordinates on numbered slots (zero at `14`). -/
def toJN : List FOp := toJ ⟨9, 10, 0, 1, 2, 3, 4, 5⟩ ⟨11, 12, 13⟩ ⟨14, 15, 16⟩ ⟨6, 7, 8⟩

open VG.Impl.Weierstrass in
/-- From Jacobian coordinates on numbered slots (zero at `14`). -/
def fromJN : List FOp := fromJ ⟨9, 10, 0, 1, 2, 3, 4, 5⟩ ⟨11, 12, 13⟩ ⟨14, 15, 16⟩ ⟨6, 7, 8⟩

theorem dblJN_ok : NumOk dblJN := ⟨by decide, by decide, by decide⟩
theorem toJN_ok : NumOk toJN := ⟨by decide, by decide, by decide⟩
theorem fromJN_ok : NumOk fromJN := ⟨by decide, by decide, by decide⟩

open VG.Impl.Weierstrass in
theorem dblJ_eq (S : RcbSlots) (p o : Pt) : dblJ S p o = ofN dblJN S p p o := rfl
open VG.Impl.Weierstrass in
theorem toJ_eq (S : RcbSlots) (p z o : Pt) : toJ S p z o = ofN toJN S p z o := rfl
open VG.Impl.Weierstrass in
theorem fromJ_eq (S : RcbSlots) (p z o : Pt) : fromJ S p z o = ofN fromJN S p z o := rfl

theorem dblJN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    (runOps dblJN e 6, runOps dblJN e 7, runOps dblJN e 8) = dblJF (e 11) (e 12) (e 13) := rfl

theorem toJN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    (runOps toJN e 6, runOps toJN e 7, runOps toJN e 8) =
      (e 11 * e 13, e 12 * (e 13 * e 13), e 13 + e 14) := rfl

theorem fromJN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    (runOps fromJN e 6, runOps fromJN e 7, runOps fromJN e 8) =
      (e 11 * e 13, e 12 + e 14, e 13 * e 13 * e 13) := rfl

end VG.Proof.Weierstrass
