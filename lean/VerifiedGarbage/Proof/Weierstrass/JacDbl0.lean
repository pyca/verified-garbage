module

public import VerifiedGarbage.Proof.Weierstrass.JacMul
import VerifiedGarbage.Proof.Weierstrass.JacAdd

/-!
# Jacobian doubling for `a = 0`

`dbl0F` is dbl-2009-l, in the order of `dblJ0` (and of
`Impl.Weierstrass.PointOps.jacDouble0`). On a curve with `a = 0` (`A0`),
the projective triple `(XZ : Y : Z³)` of its result is proportional to
Algorithm 1's double of `(XZ : Y : Z³)` (`dbl0F_cross`), so it doubles a
Jacobian triple of a point of the curve (`InvJ.dbl0`), the point at infinity
and points of order two included: their double has `Z' = 2YZ = 0`. So
`dblJ0` doubles on such a curve (`jdblOk_dblJ0`), as the additions'
case of equal points and the tables of multiples need (`JDblOk`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass

open Spec.Weierstrass VG.Impl.Weierstrass

/-- The curve's `a` is `0`. -/
def A0 (C : Curve) : Prop := (Fin.ofNat C.p C.a : Fe C) = 0

section
variable {F : Type _} [Lean.Grind.CommRing F]

/-- Jacobian doubling for `a = 0`, in the code's order. -/
def dbl0F (X Y Z : F) : F × F × F :=
  let t0 := X * X; let t1 := Y * Y; let t2 := t1 * t1
  let t3 := X + t1; let t3 := t3 * t3; let t3 := t3 - t0; let t3 := t3 - t2; let t3 := t3 + t3
  let t4 := t0 + t0; let t4 := t4 + t0
  let oz := Y * Z; let oz := oz + oz
  let ox := t4 * t4; let ox := ox - t3; let ox := ox - t3
  let oy := t3 - ox; let oy := t4 * oy
  let t2 := t2 + t2; let t2 := t2 + t2; let t2 := t2 + t2
  let oy := oy - t2
  (ox, oy, oz)

theorem dbl0F_z (X Y Z : F) : (dbl0F X Y Z).2.2 = 2 * Y * Z := by
  simp only [dbl0F]; grind

/-- On a curve with `a = 0`, `dbl0F` on `(X : Y : Z)` and Algorithm 1 on
`(XZ : Y : Z³)` twice give proportional coordinates. -/
theorem dbl0F_cross (a b b3 X Y Z : F) (ha : a = 0) (hb : b3 = 3 * b)
    (hE : Y * Y = X * X * X + a * X * Z * Z * Z * Z + b * Z * Z * Z * Z * Z * Z) :
    let j := dbl0F X Y Z
    let r := rcbAdd a b3 (X * Z) Y (Z * Z * Z) (X * Z) Y (Z * Z * Z)
    (j.1 * j.2.2) * r.2.2 = r.1 * (j.2.2 * j.2.2 * j.2.2) ∧
      j.2.1 * r.2.2 = r.2.1 * (j.2.2 * j.2.2 * j.2.2) := by
  subst ha hb
  dsimp only [dbl0F, rcbAdd]
  constructor <;> grind

end

variable {C : Curve}

/-- `dbl0F` doubles a Jacobian triple of a point of a curve with `a = 0`. -/
theorem InvJ.dbl0 (hC : Law C) (ha : A0 C) {X Y Z : Fe C} {Q : Point C}
    (hQ : onCurve C Q = true) (h : InvJ C X Y Z Q) :
    InvJ C (dbl0F X Y Z).1 (dbl0F X Y Z).2.1 (dbl0F X Y Z).2.2 (Spec.Weierstrass.add Q Q) := by
  by_cases hz : Z = 0
  · rw [(h.z_zero_iff hC).mp hz]
    exact Or.inl ⟨add_infinity_infinity, by rw [dbl0F_z, hz]; grind⟩
  by_cases hj : (dbl0F X Y Z).2.2 = 0
  · refine Or.inl ⟨?_, hj⟩
    cases Q with
    | infinity => exact absurd ((h.z_zero_iff hC).mpr rfl) hz
    | affine x y =>
      obtain ⟨-, hy⟩ := h.affine_coords hC
      rw [dbl0F_z, hy] at hj
      have h2 : (y + y) * (Z * Z * (Z * Z)) = 0 := by grind
      have hyy : y + y = 0 := by
        by_contra hne
        exact hC.mul_ne_zero hne (hC.mul_ne_zero (hC.mul_ne_zero hz hz) (hC.mul_ne_zero hz hz)) h2
      have hn : y = -y := by grind
      simp only [Spec.Weierstrass.add, ← hn, and_self, ↓reduceIte]
  · let r := rcbAdd (Fin.ofNat C.p C.a) (Fin.ofNat C.p (3 * C.b))
      (X * Z) Y (Z * Z * Z) (X * Z) Y (Z * Z * Z)
    have hr : Rep C r.1 r.2.1 r.2.2 (Spec.Weierstrass.add Q Q) :=
      hC.add hQ hQ (h.rep_of_ne hz) (h.rep_of_ne hz) rfl
    have cross := dbl0F_cross (Fin.ofNat C.p C.a) (Fin.ofNat C.p C.b) _ X Y Z ha
      (ofNat_three_mul C) (h.curve' hC hz hQ)
    exact Or.inr (hr.of_cross hC (cube_ne_zero hC hj) cross.1 cross.2)

def dblJ0N : List FOp := dblJ0 ⟨9, 10, 0, 1, 2, 3, 4, 5⟩ ⟨11, 12, 13⟩ ⟨6, 7, 8⟩

theorem dblJ0N_ok : NumOk dblJ0N := ⟨by decide, by decide, by decide⟩

theorem dblJ0_eq (S : RcbSlots) (p o : Pt) : dblJ0 S p o = ofN dblJ0N S p p o := rfl

theorem dblJ0N_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    (runOps dblJ0N e 6, runOps dblJ0N e 7, runOps dblJ0N e 8) = dbl0F (e 11) (e 12) (e 13) := by
  dsimp only [dblJ0N, dblJ0, runOps, List.foldl, FOp.run, Function.update]
  simp only [dbl0F, Prod.mk.injEq]
  constructor
  · grind
  constructor <;> grind

/-- `dblJ0` doubles on a curve with `a = 0`. -/
theorem jdblOk_dblJ0 (hC : Law C) (ha : A0 C) : JDblOk C dblJ0 :=
  ⟨dblJ0N, dblJ0N_ok, dblJ0_eq, fun e _ hQ hJ => by
    have h := dblJ0N_run e
    have h6 : runOps dblJ0N e 6 = (dbl0F (e 11) (e 12) (e 13)).1 := congrArg Prod.fst h
    have h7 : runOps dblJ0N e 7 = (dbl0F (e 11) (e 12) (e 13)).2.1 := congrArg (fun x => x.2.1) h
    have h8 : runOps dblJ0N e 8 = (dbl0F (e 11) (e 12) (e 13)).2.2 := congrArg (fun x => x.2.2) h
    rw [h6, h7, h8]
    exact InvJ.dbl0 hC ha hQ hJ⟩

end VG.Proof.Weierstrass
