module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FieldProgram
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointFormula
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG.Proof.Mont.AArch64.P521Field VG.Proof.Weierstrass

/-- Physical workspace offsets in the table's canonical-field doubling. -/
def buildDoubleOps : List PointOp := [
  .mul 1720 424 424 false,.mul 1792 3160 3160 false,
  .add 1864 2800 1720,.sub 1936 2800 1720,.mul 2008 1864 1936 false,
  .add 1864 3160 424,.mul 1936 2008 2008 false,.mul 2080 2800 1792 false,
  .mul 1864 1864 1864 false,.cms 1936 12 2080 9 1936,
  .sub 1864 1864 1720,.sub 1432 1864 1792,.mul 1720 1792 1792 false,
  .mul 2008 1936 2008 false,.cms 1288 4 2080 1 1936,.cms 1360 3 2008 8 1720]

theorem buildDouble_value {F : Type _} [Lean.Grind.CommRing F] (E : Nat → F) :
    (pointRun buildDoubleOps E 1288,pointRun buildDoubleOps E 1360,pointRun buildDoubleOps E 1432)=
      dblJF (E 2800) (E 3160) (E 424) := by
  rw [←nativeDouble_eq]
  simp only [pointRun,buildDoubleOps,List.foldl,PointOp.run,Function.update_apply,nativeDouble,
    VG.Proof.Weierstrass.Cms.smulN,ite_true]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> grind

theorem buildDouble_reads : fieldReads buildDoubleOps [2800,3160,424]=true := by decide

def buildSlot (d : Nat) : Prop := d%72=64 ∧ d+72≤3304

theorem build_field_layout : FieldLayout id buildSlot := by
  constructor
  · intro x hx; exact hx.2
  · intro x hx
    have h := Nat.mod_add_div x 72
    rw [hx.1] at h
    change x%8=0
    omega_arith
  · intro x y hx hy hn
    have mx := hx.1
    have my := hy.1
    change x+72≤y ∨ y+72≤x
    omega_arith

theorem buildDouble_slots : ∀op∈buildDoubleOps,∀x∈op.out::op.ins,buildSlot x := by
  simp [buildDoubleOps,PointOp.out,PointOp.ins,buildSlot]

theorem buildDouble_coeffs : ∀op∈buildDoubleOps,fieldCoeffs op := by
  simp [buildDoubleOps,fieldCoeffs]

end VG.Proof.Weierstrass.AArch64.P521Native
