module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildDouble
public import VerifiedGarbage.Proof.Weierstrass.Env

/-! Complete final addition in the ordinary P-521 field. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG.Impl.Weierstrass VG.Proof.Weierstrass VG.Proof.Mont.AArch64.P521Field

def finishAddSlotMap : RcbSlots := ⟨496,568,1720,1792,1864,1936,2008,2080⟩
def finishAddP : Pt := ⟨1072,1144,1216⟩
def finishAddQ : Pt := ⟨1504,1576,1648⟩
def finishAddOut : Pt := ⟨1288,1360,1432⟩

def finishPointOp : FOp → PointOp
  | .mul o a b => .mul o a b false
  | .add o a b => .add o a b
  | .sub o a b => .sub o a b

def finishAddOps : List PointOp :=
  (rcb3 finishAddSlotMap finishAddP finishAddQ finishAddOut).map finishPointOp

theorem finishAdd_reads : fieldReads finishAddOps [1072,1144,1216,1504,1576,1648,568]=true := by decide

theorem finishAdd_slots : ∀op∈finishAddOps,∀x∈op.out::op.ins,buildSlot x := by
  simp [finishAddOps,finishPointOp,rcb3,finishAddSlotMap,finishAddP,finishAddQ,finishAddOut,PointOp.out,PointOp.ins,buildSlot]

theorem finishAdd_coeffs : ∀op∈finishAddOps,fieldCoeffs op := by
  simp [finishAddOps,finishPointOp,rcb3,finishAddSlotMap,finishAddP,finishAddQ,finishAddOut,fieldCoeffs]

theorem finishAdd_value {F : Type _} [Lean.Grind.CommRing F] (E : Nat → F) :
    (pointRun finishAddOps E 1288,pointRun finishAddOps E 1360,pointRun finishAddOps E 1432)=
      rcbAdd3 (E 568) (E 1072) (E 1144) (E 1216) (E 1504) (E 1576) (E 1648) := by
  simp only [pointRun,finishAddOps,finishPointOp,rcb3,finishAddSlotMap,finishAddP,finishAddQ,finishAddOut,
    List.map_cons,List.map_nil,List.foldl,PointOp.run,Function.update_apply,ite_true]
  rfl

end VG.Proof.Weierstrass.AArch64.P521Native
