module

-- separate module: the doubling of every curve whose `a` is neither 0 nor -3, which the windows of
-- each such curve's `vg_<curve>_mul` share (brainpoolP512r1's, and the other brainpool curves')

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.WindowA
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.Proof.Weierstrass.JacDblAF

/-!
# Jacobian doubling for any `a`

`WindowA.dblJa` (RISC-V's) on numbered slots: `dblJaN_run`, its operations
compute `dblAF` (`JacDblAF.lean`, the formulas and their proof) of the slot
`9`'s `a`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass

open Spec.Weierstrass VG.Impl.Weierstrass VG.Impl.Ecdsa.RISCV64.WindowA

/-- `dblJa` on numbered slots: `a` at 9, `p` at 11–13, `o` at 6–8. -/
def dblJaN : List FOp := dblJa ⟨9, 10, 0, 1, 2, 3, 4, 5⟩ ⟨11, 12, 13⟩ ⟨6, 7, 8⟩

theorem dblJaN_ok : NumOk dblJaN := ⟨by decide, by decide, by decide⟩

theorem dblJa_eq (S : RcbSlots) (p o : Pt) : dblJa S p o = ofN dblJaN S p p o := rfl

theorem dblJaN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    (runOps dblJaN e 6, runOps dblJaN e 7, runOps dblJaN e 8) = dblAF (e 9) (e 11) (e 12) (e 13) := by
  dsimp only [dblJaN, dblJa, runOps, List.foldl, FOp.run, Function.update]
  simp only [dblAF, Prod.mk.injEq]
  constructor
  · grind
  constructor <;> grind

end VG.Proof.Weierstrass
