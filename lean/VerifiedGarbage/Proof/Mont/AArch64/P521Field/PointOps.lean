module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.OrdinaryEnv
public import VerifiedGarbage.Proof.Weierstrass.JacMadd
public import VerifiedGarbage.Proof.Weierstrass.Cms

/-! ### `Mont.AArch64.P521Field.PointFormula`, which this module and modules that import it used -/

section

/-! The fused schedules compute the existing Jacobian point formulas. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Cms

section
variable {F : Type _} [Lean.Grind.CommRing F]

/-- Doubling in the measured instruction schedule's order. -/
def nativeDouble (X Y Z : F) : F × F × F :=
  let z2 := Z*Z
  let y2 := Y*Y
  let t1 := X+z2
  let t2 := X-z2
  let x2p := t1*t2
  let t1 := Y+Z
  let x4p := x2p*x2p
  let xy2 := X*y2
  let t2 := t1*t1
  let d := smulN 12 xy2-smulN 9 x4p
  let t1 := t2-z2
  let y4 := y2*y2
  let oz := t1-y2
  let dx2 := d*x2p
  let ox := smulN 4 xy2-d
  let oy := smulN 3 dx2-smulN 8 y4
  (ox,oy,oz)

theorem nativeDouble_eq (X Y Z : F) : nativeDouble X Y Z=dblJF X Y Z := by
  simp only [nativeDouble,dblJF,smulN]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> grind

/-- Mixed addition in the measured instruction schedule's order. -/
def nativeMixed (X Y Z x y : F) : F × F × F :=
  let zp2 := Z*Z
  let y2a := Z*y
  let x2a := zp2*x
  let y2a := zp2*y2a
  let xd := x2a-X
  let yd := y2a-Y
  let zz := xd*xd
  let ww := yd*yd
  let zzx1 := zz*X
  let zzx2 := zz*x2a
  let resx := ww-zzx1
  let t1 := zzx2-zzx1
  let resz := xd*Z
  let resx := resx-zzx2
  let t2 := zzx1-resx
  let t1 := t1*Y
  let t2 := yd*t2
  let resy := t2-t1
  (resx,resy,resz)

theorem nativeMixed_eq (X Y Z x y : F) : nativeMixed X Y Z x y=maddJF X Y Z x y := by
  simp only [nativeMixed,maddJF]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> grind

end
end VG.Proof.Mont.AArch64.P521Field

end

end

/-! ### `Mont.AArch64.P521Field.OrdinaryUpdate`, which this module and modules that import it used -/

section

/-! Lift arithmetic postconditions to updates of ordinary-field slot environments. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Weierstrass

section
variable {base : Addr} {p : Nat} [NeZero p] {loc : Nat → Nat} {V : List Nat}
  {E : Nat → Fin p} {caps : Nat → Nat} {s t : State} {o cap a b : Nat}
  (h : OrdinaryInv base p loc V E caps s) (ha : a∈V) (hb : b∈V)
  (outside : Outside base (loc o) 72 s.mem t.mem)
  (apart : ∀x∈V,x≠o → loc x+72≤loc o ∨ loc o+72≤loc x) (fits : ∀x∈V,loc x+72≤2^64)
  (bound : wordsVal t.mem base (loc o) 9<cap*p)

include h ha hb outside apart fits bound

theorem OrdinaryInv.mul_update
    (value : wordsVal t.mem base (loc o) 9%p=wordsVal s.mem base (loc a) 9*wordsVal s.mem base (loc b) 9%p) :
    OrdinaryInv base p loc (o::V) (Function.update E o (E a*E b)) (Function.update caps o cap) t := by
  refine h.update outside apart fits bound ?_
  have e : Fin.ofNat p (wordsVal t.mem base (loc o) 9)=Fin.ofNat p (wordsVal s.mem base (loc a) 9*wordsVal s.mem base (loc b) 9) :=
    ofNat_eq_ofNat.mpr value
  rw [ofNat_mul',h.value a ha,h.value b hb] at e
  exact e

theorem OrdinaryInv.add_update
    (value : wordsVal t.mem base (loc o) 9=(wordsVal s.mem base (loc a) 9+wordsVal s.mem base (loc b) 9)%p) :
    OrdinaryInv base p loc (o::V) (Function.update E o (E a+E b)) (Function.update caps o cap) t := by
  refine h.update outside apart fits bound ?_
  rw [value,ordinary_add,h.value a ha,h.value b hb]

theorem OrdinaryInv.sub_update
    (bBound : wordsVal s.mem base (loc b) 9≤wordsVal s.mem base (loc a) 9+p)
    (value : wordsVal t.mem base (loc o) 9=(wordsVal s.mem base (loc a) 9+p-wordsVal s.mem base (loc b) 9)%p) :
    OrdinaryInv base p loc (o::V) (Function.update E o (E a-E b)) (Function.update caps o cap) t := by
  refine h.update outside apart fits bound ?_
  rw [value,ordinary_sub bBound,h.value a ha,h.value b hb]

theorem OrdinaryInv.cms_update (C D : Nat) (bBound : wordsVal s.mem base (loc b) 9≤p)
    (value : wordsVal t.mem base (loc o) 9=(C*wordsVal s.mem base (loc a) 9+D*(p-wordsVal s.mem base (loc b) 9))%p) :
    OrdinaryInv base p loc (o::V) (Function.update E o (Cms.smulN C (E a)-Cms.smulN D (E b)))
      (Function.update caps o cap) t := by
  refine h.update outside apart fits bound ?_
  rw [value,ordinary_cms C _ D _ bBound,h.value a ha,h.value b hb]

end
end VG.Proof.Mont.AArch64.P521Field

end

end

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
