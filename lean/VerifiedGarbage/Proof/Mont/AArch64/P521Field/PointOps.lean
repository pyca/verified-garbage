module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointFormula
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.OrdinaryUpdate

/-! Fused point schedules on labelled ordinary-field slots, including weak ranges. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Cms

inductive PointOp where
  | mul (o a b : Nat) (weak : Bool)
  | add (o a b : Nat)
  | sub (o a b : Nat)
  | cms (o C a D b : Nat)

def PointOp.out : PointOp → Nat
  | .mul o _ _ _ | .add o _ _ | .sub o _ _ | .cms o _ _ _ _ => o

def PointOp.ins : PointOp → List Nat
  | .mul _ a b _ | .add _ a b | .sub _ a b | .cms _ _ a _ b => [a,b]

def PointOp.cap : PointOp → Nat
  | .mul _ _ _ true => 2
  | _ => 1

def PointOp.run {F : Type _} [Lean.Grind.CommRing F] : PointOp → (Nat → F) → Nat → F
  | .mul o a b _,E => Function.update E o (E a*E b)
  | .add o a b,E => Function.update E o (E a+E b)
  | .sub o a b,E => Function.update E o (E a-E b)
  | .cms o C a D b,E => Function.update E o (smulN C (E a)-smulN D (E b))

def pointRun {F : Type _} [Lean.Grind.CommRing F] (ops : List PointOp) (E : Nat → F) : Nat → F :=
  ops.foldl (fun E op => op.run E) E

/-- Inputs 0..2, outputs 3..5, and seven reusable temporary slots 6..12. -/
def doubleOps : List PointOp := [
  .mul 6 2 2 false,.mul 7 1 1 false,.add 11 0 6,.sub 10 0 6,
  .mul 8 11 10 false,.add 11 1 2,.mul 12 8 8 false,.mul 9 0 7 true,
  .mul 10 11 11 false,.cms 12 12 9 9 12,.sub 11 10 6,.mul 10 7 7 false,
  .sub 5 11 7,.mul 11 12 8 true,.cms 3 4 9 1 12,.cms 4 3 11 8 10]

theorem doubleOps_value {F : Type _} [Lean.Grind.CommRing F] (E : Nat → F) :
    (pointRun doubleOps E 3,pointRun doubleOps E 4,pointRun doubleOps E 5)=dblJF (E 0) (E 1) (E 2) := by
  rw [←nativeDouble_eq]
  simp only [pointRun,doubleOps,List.foldl,PointOp.run,Function.update_apply,nativeDouble,smulN,
    ite_true]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> grind

/-- Every read is initialized, and each operation admits its inputs' live range bounds. -/
def pointReadsOk : List PointOp → List Nat → (Nat → Nat) → Bool
  | [],_,_ => true
  | op::ops,V,caps =>
    let allowed := match op with
      | .cms _ _ a _ b => caps a≤2 && caps b≤1
      | _ => op.ins.all (fun x => caps x≤1)
    op.ins.all (fun x => decide (x∈V)) && allowed &&
      pointReadsOk ops (op.out::V) (Function.update caps op.out op.cap)

theorem doubleOps_reads : pointReadsOk doubleOps [0,1,2] (fun _ => 1)=true := by decide

end VG.Proof.Mont.AArch64.P521Field
