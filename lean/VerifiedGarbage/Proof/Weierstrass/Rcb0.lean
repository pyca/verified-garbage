module

public import VerifiedGarbage.Impl.Weierstrass.Rcb0
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.Law3

/-!
# Complete formulas for `a = 0`, and the ladder's step with them

Algorithms 8 (an affine point's addition) and 9 (doubling) of Renes,
Costello and Batina, as `Impl/Weierstrass/Rcb0.lean`'s code computes them
(`rcbAdd0m`, `rcbDbl0`), over any commutative ring of Lean's core, are
Algorithm 1 for `a = 0`: Algorithm 8 with `Z₂ = 1` (`rcbAdd0m_eq`), and
Algorithm 9 for a point and itself on `Y²Z = X³ + bZ³` (`rcbDbl0_eq`). On
numbered slots (`rcb0mN`, `dbl0N`), as `ofN_ok` takes them, and so are the ladders'
(`ladOps`).

A ladder's iteration doubles and adds either by Algorithm 1 or, for a curve
with `a = 0` and an affine point, by Algorithms 9 and 8 (`ladDbl`, `ladAdd`,
chosen by `a0`), and either keeps a representative of `[k >>> j]P`
(`ladder_step'`).
-/

-- separate module: the formulas are every target's, and `Rcb.lean`'s and `Env.lean`'s
-- importers would all be rebuilt for what only the ladders of curves with `a = 0` use.

@[expose] public section

namespace VG.Proof.Weierstrass

open VG.Impl.Weierstrass Spec.Weierstrass

section Ring

variable {F : Type _} [Lean.Grind.CommRing F]

/-- Algorithm 8 (`a = 0`, the second point `(X₂ : Y₂ : 1)`), in its stated
order, with `3b`. -/
def rcbAdd0m (b3 X1 Y1 Z1 X2 Y2 : F) : F × F × F :=
  let t0 := X1 * X2; let t1 := Y1 * Y2; let t3 := X2 + Y2; let t4 := X1 + Y1; let t3 := t3 * t4
  let t4 := t0 + t1; let t3 := t3 - t4; let t4 := Y2 * Z1; let t4 := t4 + Y1; let Y3 := X2 * Z1
  let Y3 := Y3 + X1; let X3 := t0 + t0; let t0 := X3 + t0; let t2 := b3 * Z1; let Z3 := t1 + t2
  let t1 := t1 - t2; let Y3 := b3 * Y3; let X3 := t4 * Y3; let t2 := t3 * t1; let X3 := t2 - X3
  let Y3 := Y3 * t0; let t1 := t1 * Z3; let Y3 := t1 + Y3; let t0 := t0 * t3; let Z3 := Z3 * t4
  let Z3 := Z3 + t0
  (X3, Y3, Z3)

/-- Algorithm 8 is Algorithm 1 with `a = 0` and `Z₂ = 1`. -/
theorem rcbAdd0m_eq (b3 X1 Y1 Z1 X2 Y2 : F) :
    rcbAdd0m b3 X1 Y1 Z1 X2 Y2 = rcbAdd 0 b3 X1 Y1 Z1 X2 Y2 1 := by
  simp only [rcbAdd0m, rcbAdd, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> grind

/-- Algorithm 9 (doubling, `a = 0`), in its stated order, with `3b`. -/
def rcbDbl0 (b3 X Y Z : F) : F × F × F :=
  let t0 := Y * Y; let Z3 := t0 + t0; let Z3 := Z3 + Z3; let Z3 := Z3 + Z3; let t1 := Y * Z
  let t2 := Z * Z; let t2 := b3 * t2; let X3 := t2 * Z3; let Y3 := t0 + t2; let Z3 := t1 * Z3
  let t1 := t2 + t2; let t2 := t1 + t2; let t0 := t0 - t2; let Y3 := t0 * Y3; let Y3 := X3 + Y3
  let t1 := X * Y; let X3 := t0 * t1; let X3 := X3 + X3
  (X3, Y3, Z3)

/-- Algorithm 9 is Algorithm 1's sum of a point and itself, for a point of
`Y²Z = X³ + bZ³`. -/
theorem rcbDbl0_eq (b X Y Z : F) (hE : Y * Y * Z = X * X * X + b * Z * Z * Z) :
    rcbDbl0 (3 * b) X Y Z = rcbAdd 0 (3 * b) X Y Z X Y Z := by
  simp only [rcbDbl0, rcbAdd, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> grind

/-- The ladder's doubling: Algorithm 9 for `a0`, else Algorithm 1. -/
def ladDbl (a0 : Bool) (a b3 X Y Z : F) : F × F × F :=
  if a0 then rcbDbl0 b3 X Y Z else rcbAdd a b3 X Y Z X Y Z

/-- The ladder's addition of `(X₂ : Y₂ : Z₂)`: Algorithm 8 for `a0` (which
takes `Z₂` to be one), else Algorithm 1. -/
def ladAdd (a0 : Bool) (a b3 X1 Y1 Z1 X2 Y2 Z2 : F) : F × F × F :=
  if a0 then rcbAdd0m b3 X1 Y1 Z1 X2 Y2 else rcbAdd a b3 X1 Y1 Z1 X2 Y2 Z2

end Ring

/-! ## On numbered slots -/

/-- Algorithm 8 on numbered slots (`q.z`, slot 16, not read). -/
def rcb0mN : List FOp := rcb0m ⟨9, 10, 0, 1, 2, 3, 4, 5⟩ ⟨11, 12, 13⟩ ⟨14, 15, 16⟩ ⟨6, 7, 8⟩

theorem rcb0mN_ok : NumOk rcb0mN := ⟨by decide, by decide, by decide⟩

theorem rcb0m_eq (S : RcbSlots) (p q o : Pt) : rcb0m S p q o = ofN rcb0mN S p q o := rfl

theorem rcb0mN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    (runOps rcb0mN e 6, runOps rcb0mN e 7, runOps rcb0mN e 8) =
      rcbAdd0m (e 10) (e 11) (e 12) (e 13) (e 14) (e 15) := rfl

/-- Algorithm 9 on numbered slots (the second point's, `14 … 16`, not read). -/
def dbl0N : List FOp := dbl0 ⟨9, 10, 0, 1, 2, 3, 4, 5⟩ ⟨11, 12, 13⟩ ⟨6, 7, 8⟩

theorem dbl0N_ok : NumOk dbl0N := ⟨by decide, by decide, by decide⟩

theorem dbl0_eq (S : RcbSlots) (p o : Pt) : dbl0 S p o = ofN dbl0N S p p o := rfl

theorem dbl0N_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    (runOps dbl0N e 6, runOps dbl0N e 7, runOps dbl0N e 8) = rcbDbl0 (e 10) (e 11) (e 12) (e 13) := rfl

theorem rcbN_ok : NumOk rcbN := ⟨rcbN_out, by decide, rcbN_reads⟩

/-- The ladder's formulas on numbered slots (`Env.lean`), which compute
`ladDbl` and `ladAdd` on the ladder's. -/
theorem ladOps (C : Curve) (L : LadderCfg) (a0 : Bool) : ∃ N₁ N₂, NumOk N₁ ∧ NumOk N₂ ∧
    ladDblOps L a0 = ofN N₁ L.S L.R L.R L.D ∧ ladAddOps L a0 = ofN N₂ L.S L.D L.G L.T ∧
    (∀ E : Nat → Fe C, (runOps N₁ (fun y => E (rcbσ L.S L.R L.R L.D y)) 6,
      runOps N₁ (fun y => E (rcbσ L.S L.R L.R L.D y)) 7, runOps N₁ (fun y => E (rcbσ L.S L.R L.R L.D y)) 8) =
        ladDbl a0 (E L.S.a) (E L.S.b3) (E L.R.x) (E L.R.y) (E L.R.z)) ∧
    (∀ E : Nat → Fe C, (runOps N₂ (fun y => E (rcbσ L.S L.D L.G L.T y)) 6,
      runOps N₂ (fun y => E (rcbσ L.S L.D L.G L.T y)) 7, runOps N₂ (fun y => E (rcbσ L.S L.D L.G L.T y)) 8) =
        ladAdd a0 (E L.S.a) (E L.S.b3) (E L.D.x) (E L.D.y) (E L.D.z) (E L.G.x) (E L.G.y) (E L.G.z)) := by
  cases a0
  · exact ⟨rcbN, rcbN, rcbN_ok, rcbN_ok, rfl, rfl, fun _ => rcbN_run _, fun _ => rcbN_run _⟩
  · exact ⟨dbl0N, rcb0mN, dbl0N_ok, rcb0mN_ok, rfl, rfl, fun _ => dbl0N_run _, fun _ => rcb0mN_run _⟩

/-! ## The ladder's step -/

variable {C : Curve}

/-- An iteration of the ladder keeps a representative of `[k >>> j]P`, by
Algorithm 1, or for a curve with `a = 0` and `P`'s representative's `Z`
one, by Algorithms 9 and 8 (`ladder_step`, as they are Algorithm 1 there). -/
theorem ladder_step' (hC : Law C) {P : Point C} (hP : onCurve C P = true) {k j : Nat} {a0 : Bool}
    {Px Py Pz X Y Z X2 Y2 Z2 X3 Y3 Z3 : Fe C}
    (h0 : a0 = true → (Fin.ofNat C.p C.a : Fe C) = 0 ∧ Pz = 1)
    (hPr : Rep C Px Py Pz P) (hR : Rep C X Y Z (mul (k >>> (j + 1)) P))
    (h2 : ladDbl a0 (Fin.ofNat C.p C.a) (Fin.ofNat C.p (3 * C.b)) X Y Z = (X2, Y2, Z2))
    (h3 : ladAdd a0 (Fin.ofNat C.p C.a) (Fin.ofNat C.p (3 * C.b)) X2 Y2 Z2 Px Py Pz = (X3, Y3, Z3)) :
    Rep C (if k.testBit j then X3 else X2) (if k.testBit j then Y3 else Y2)
      (if k.testBit j then Z3 else Z2) (mul (k >>> j) P) := by
  cases a0 with
  | false => exact ladder_step hC hP hPr hR h2 h3
  | true =>
    obtain ⟨ha, hz⟩ := h0 rfl
    have hE := hR.proj (hC.onCurve_mul hP _)
    rw [ha] at hE
    refine ladder_step hC hP hPr hR ?_ ?_
    · rw [ha, ofNat_three_mul, ← rcbDbl0_eq _ _ _ _ (by grind), ← ofNat_three_mul]
      exact h2
    · rw [ha, hz, ← rcbAdd0m_eq]
      exact h3

end VG.Proof.Weierstrass
