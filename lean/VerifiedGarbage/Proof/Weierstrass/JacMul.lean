import VerifiedGarbage.Impl.Weierstrass.JacMul
import VerifiedGarbage.Proof.Weierstrass.Jac

/-! Jacobian doubling with a direct product for `2YZ`. -/
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

end VG.Proof.Weierstrass
