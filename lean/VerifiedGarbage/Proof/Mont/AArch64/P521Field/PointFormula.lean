module

public import VerifiedGarbage.Proof.Weierstrass.JacMadd
public import VerifiedGarbage.Proof.Weierstrass.Cms

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
