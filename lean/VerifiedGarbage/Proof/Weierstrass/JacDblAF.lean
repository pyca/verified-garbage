module

public import VerifiedGarbage.Proof.Weierstrass.Jac
import VerifiedGarbage.Proof.Weierstrass.JacAdd

/-!
# Jacobian doubling for any `a`: the formulas

`dblAF` is dbl-2007-bl, with `a` an argument. On a curve with that `a`, the
projective triple `(XZ : Y : Z³)` of its result is proportional to
Algorithm 1's double of `(XZ : Y : Z³)` (`dblAF_cross`), so it doubles a
Jacobian triple of a point of the curve (`InvJ.dblA`), the point at
infinity and points of order two included: their double has
`Z' = 2YZ = 0`. Every target's code of this doubling reads `a` from a slot
and computes `dblAF` of it: RISC-V's `WindowA.dblJa` (`JacDblA.lean`) and
x86-64's `WinCfg.dblJGen` (`X86_64/WindowGeneral.lean`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

section
variable {F : Type _} [Lean.Grind.CommRing F]

/-- Jacobian doubling for any `a`, in the code's order. -/
def dblAF (A X Y Z : F) : F × F × F :=
  let t0 := X * X; let t1 := Y * Y; let t2 := t1 * t1
  let t3 := X + t1; let t3 := t3 * t3; let t3 := t3 - t0; let t3 := t3 - t2; let t3 := t3 + t3
  let t4 := Z * Z; let t4 := t4 * t4; let t4 := A * t4; let t5 := t0 + t0; let t5 := t5 + t0
  let t4 := t4 + t5
  let oz := Y * Z; let oz := oz + oz
  let ox := t4 * t4; let ox := ox - t3; let ox := ox - t3
  let oy := t3 - ox; let oy := t4 * oy
  let t2 := t2 + t2; let t2 := t2 + t2; let t2 := t2 + t2
  let oy := oy - t2
  (ox, oy, oz)

theorem dblAF_z (A X Y Z : F) : (dblAF A X Y Z).2.2 = 2 * Y * Z := by
  simp only [dblAF]; grind

/-- `dblAF` on `(X : Y : Z)` and Algorithm 1 on `(XZ : Y : Z³)` twice give
proportional coordinates, for a point of `Y² = X³ + a X Z⁴ + b Z⁶`. -/
theorem dblAF_cross (a b b3 X Y Z : F) (hb : b3 = 3 * b)
    (hE : Y * Y = X * X * X + a * X * Z * Z * Z * Z + b * Z * Z * Z * Z * Z * Z) :
    let j := dblAF a X Y Z
    let r := rcbAdd a b3 (X * Z) Y (Z * Z * Z) (X * Z) Y (Z * Z * Z)
    (j.1 * j.2.2) * r.2.2 = r.1 * (j.2.2 * j.2.2 * j.2.2) ∧
      j.2.1 * r.2.2 = r.2.1 * (j.2.2 * j.2.2 * j.2.2) := by
  subst hb
  dsimp only [dblAF, rcbAdd]
  constructor <;> grind

end

variable {C : Curve}

/-- `dblAF` of the curve's `a` doubles a Jacobian triple of a point of it. -/
theorem InvJ.dblA (hC : Law C) {X Y Z : Fe C} {Q : Point C}
    (hQ : onCurve C Q = true) (h : InvJ C X Y Z Q) :
    InvJ C (dblAF (Fin.ofNat C.p C.a) X Y Z).1 (dblAF (Fin.ofNat C.p C.a) X Y Z).2.1
      (dblAF (Fin.ofNat C.p C.a) X Y Z).2.2 (Spec.Weierstrass.add Q Q) := by
  by_cases hz : Z = 0
  · rw [(h.z_zero_iff hC).mp hz]
    exact Or.inl ⟨add_infinity_infinity, by rw [dblAF_z, hz]; grind⟩
  by_cases hj : (dblAF (Fin.ofNat C.p C.a) X Y Z).2.2 = 0
  · refine Or.inl ⟨?_, hj⟩
    cases Q with
    | infinity => exact absurd ((h.z_zero_iff hC).mpr rfl) hz
    | affine x y =>
      obtain ⟨-, hy⟩ := h.affine_coords hC
      rw [dblAF_z, hy] at hj
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
    have cross := dblAF_cross (Fin.ofNat C.p C.a) (Fin.ofNat C.p C.b) _ X Y Z
      (ofNat_three_mul C) (h.curve' hC hz hQ)
    exact Or.inr (hr.of_cross hC (cube_ne_zero hC hj) cross.1 cross.2)

/-- `InvJ.dblA` for coordinates given as `dblAF` of a value of `a`. -/
theorem InvJ.dblA' (hC : Law C) {A X Y Z X' Y' Z' : Fe C} {Q : Point C}
    (hQ : onCurve C Q = true) (h : InvJ C X Y Z Q) (ha : A = Fin.ofNat C.p C.a)
    (e : (X', Y', Z') = dblAF A X Y Z) : InvJ C X' Y' Z' (Spec.Weierstrass.add Q Q) := by
  subst ha
  simp only [Prod.ext_iff] at e
  obtain ⟨ex, ey, ez⟩ := e
  rw [ex, ey, ez]
  exact InvJ.dblA hC hQ h

end VG.Proof.Weierstrass
