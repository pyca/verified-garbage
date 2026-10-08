import VerifiedGarbage.Proof.Weierstrass.JacMul

/-! The fused small linear combinations implement the existing Jacobian double. -/
namespace VG.Proof.P256.EcdhDouble
open VG.Proof.Weierstrass

variable {F : Type _} [Lean.Grind.CommRing F]

def values (X Y Z : F) : F × F × F :=
  let zz := Z*Z
  let yy := Y*Y
  let m := (X+zz)*(X-zz)
  let xy := X*yy
  let d := 12*xy-9*(m*m)
  (4*xy-d,3*(d*m)-8*(yy*yy),(Y+Z)*(Y+Z)-zz-yy)

theorem values_eq (X Y Z : F) : values X Y Z=dblJF X Y Z := by
  simp only [values,dblJF,Prod.mk.injEq]
  constructor
  · grind
  constructor <;> grind

end VG.Proof.P256.EcdhDouble
