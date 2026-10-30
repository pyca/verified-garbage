module

public import VerifiedGarbage.Impl.Weierstrass.JacMul
public import VerifiedGarbage.Proof.Weierstrass.Jac

/-! Jacobian doubling with a direct product for `2YZ`. -/

@[expose] public section

namespace VG.Proof.Weierstrass
open VG.Impl.Weierstrass

def dblJMulN : List FOp := dblJMul ⟨9, 10, 0, 1, 2, 3, 4, 5⟩ ⟨11, 12, 13⟩ ⟨6, 7, 8⟩

def dblJChoiceN (direct : Bool) : List FOp := if direct then dblJMulN else dblJN

theorem dblJChoiceN_ok (direct : Bool) : NumOk (dblJChoiceN direct) := by
  cases direct <;> exact ⟨by decide, by decide, by decide⟩

theorem dblJChoice_eq (direct : Bool) (S : RcbSlots) (p o : Pt) :
    (if direct then dblJMul S p o else dblJ S p o) = ofN (dblJChoiceN direct) S p p o := by
  cases direct <;> rfl

theorem dblJMulN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    (runOps dblJMulN e 6, runOps dblJMulN e 7, runOps dblJMulN e 8) =
      dblJF (e 11) (e 12) (e 13) := by
  dsimp only [dblJMulN, dblJMul, runOps, List.foldl, FOp.run, Function.update]
  simp only [dblJF, Prod.mk.injEq]
  constructor
  · grind
  constructor <;> grind

theorem dblJChoiceN_run {F : Type _} [Lean.Grind.CommRing F] (direct : Bool) (e : Nat → F) :
    (runOps (dblJChoiceN direct) e 6, runOps (dblJChoiceN direct) e 7,
      runOps (dblJChoiceN direct) e 8) = dblJF (e 11) (e 12) (e 13) := by
  cases direct
  · exact dblJN_run e
  · exact dblJMulN_run e

def dblJSN : List FOp := dblJS ⟨9, 10, 0, 1, 2, 3, 4, 5⟩ ⟨11, 12, 13⟩ ⟨6, 7, 8⟩

def dblJSChoiceN (direct : Bool) : List FOp := if direct then dblJMulN else dblJSN

theorem dblJSChoiceN_ok (direct : Bool) : NumOk (dblJSChoiceN direct) := by
  cases direct <;> exact ⟨by decide, by decide, by decide⟩

theorem dblJSChoice_eq (direct : Bool) (S : RcbSlots) (p o : Pt) :
    (if direct then dblJMul S p o else dblJS S p o) = ofN (dblJSChoiceN direct) S p p o := by
  cases direct <;> rfl

theorem dblJSN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    (runOps dblJSN e 6, runOps dblJSN e 7, runOps dblJSN e 8) =
      dblJF (e 11) (e 12) (e 13) := by
  dsimp only [dblJSN, dblJS, runOps, List.foldl, FOp.run, Function.update]
  simp only [dblJF, Prod.mk.injEq]
  constructor
  · grind
  constructor <;> grind

theorem dblJSChoiceN_run {F : Type _} [Lean.Grind.CommRing F] (direct : Bool) (e : Nat → F) :
    (runOps (dblJSChoiceN direct) e 6, runOps (dblJSChoiceN direct) e 7,
      runOps (dblJSChoiceN direct) e 8) = dblJF (e 11) (e 12) (e 13) := by
  cases direct
  · exact dblJSN_run e
  · exact dblJMulN_run e

/-- `dbl` doubles a Jacobian point of `C`: the same numbered field
operations `N` (`ofN`) wherever it runs, which, from a Jacobian triple of a
point of `C` in `p` (`11`–`13`), leave one of its double in `o` (`6`–`8`).
What the additions' case of equal points and the tables of multiples need
of the curve's `a`: `dblJMul` for `a = -3` (`jdblOk_dblJMul`). -/
def JDblOk (C : Spec.Weierstrass.Curve) (dbl : RcbSlots → Pt → Pt → List FOp) : Prop :=
  ∃ N : List FOp, NumOk N ∧ (∀ S p o, dbl S p o = ofN N S p p o) ∧
    ∀ (e : Nat → Spec.Weierstrass.Fe C) {Q : Spec.Weierstrass.Point C},
      Spec.Weierstrass.onCurve C Q = true → InvJ C (e 11) (e 12) (e 13) Q →
      InvJ C (runOps N e 6) (runOps N e 7) (runOps N e 8) (Spec.Weierstrass.add Q Q)

/-- `dbl` is the same numbered field operations `N` (`ofN`) wherever it
runs: what the proofs of constant time need of a doubling. -/
def JDblShape (dbl : RcbSlots → Pt → Pt → List FOp) : Prop :=
  ∃ N : List FOp, NumOk N ∧ ∀ S p o, dbl S p o = ofN N S p p o

theorem JDblOk.shape {C : Spec.Weierstrass.Curve} {dbl : RcbSlots → Pt → Pt → List FOp}
    (h : JDblOk C dbl) : JDblShape dbl :=
  let ⟨N, hN, he, _⟩ := h
  ⟨N, hN, he⟩

theorem jdblShape_dblJMul : JDblShape dblJMul :=
  ⟨dblJChoiceN true, dblJChoiceN_ok true, dblJChoice_eq true⟩

/-- `dblJMul` doubles on a curve with `a = -3`. -/
theorem jdblOk_dblJMul {C : Spec.Weierstrass.Curve} (hC : Law C) (ha : AM3 C) : JDblOk C dblJMul :=
  ⟨dblJChoiceN true, dblJChoiceN_ok true, dblJChoice_eq true,
    fun e _ hQ hJ => InvJ.dbl' hC ha hQ hJ (dblJChoiceN_run true e)⟩

end VG.Proof.Weierstrass
