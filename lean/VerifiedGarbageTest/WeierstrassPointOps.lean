module

import Lean.Elab.Command
meta import Lean.Elab.Command
import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
meta import VerifiedGarbage.Proof.Weierstrass.PointOpsContract

/-!
# The point formulas of `Proof/Weierstrass/PointOpsContract.lean`

Each formula gives the point SEC 1's group law (`Spec.Weierstrass.add`)
does, on P-224, P-256, P-384 and P-521 (`a = -3`, with `jacDouble`) and
secp256k1 (`a = 0`, with `jacDouble0`): for `P` and `Q` among the point at
infinity, small multiples of the base point and their negations (so that
`P = Q` and `P = -Q` arise), each in Jacobian or projective coordinates
scaled by factors other than one, so that `Z ≠ 1`:

* the curve's doubling `dbl P` is `P + P`;
* `jacAddCached P Q Z₂² Z₂³ dbl` and, for `Q` affine (`Z = 1`),
  `jacAddAffine P Q dbl` are `P + Q`;
* for `a = -3`, `rcbAdd b P Q` and, for `Q` affine, `rcbAddAffine b P Q`
  are `P + Q`.
-/

namespace VG.Test.WeierstrassPointOps

open Lean Elab Command Spec.Weierstrass
open Impl.Weierstrass.PointOps (jacDouble jacDouble0 jacAddCached jacAddAffine rcbAddAffine rcbAdd)

variable {C : Spec.Weierstrass.Curve}

/-- `P` in Jacobian coordinates scaled by `l`: `(l² x : l³ y : l)`, and
`(l² : l³ : 0)` for the point at infinity. -/
def toJac (l : Fe C) : Point C → Fe C × Fe C × Fe C
  | .infinity => (l * l, l * l * l, 0)
  | .affine x y => (l * l * x, l * l * l * y, l)

/-- `P` in projective coordinates scaled by `l`: `(l x : l y : l)`, and
`(0 : l : 0)` for the point at infinity. -/
def toProj (l : Fe C) : Point C → Fe C × Fe C × Fe C
  | .infinity => (0, l, 0)
  | .affine x y => (l * x, l * y, l)

/-- The point of Jacobian coordinates: `(X / Z², Y / Z³)`, or the point at
infinity for `Z = 0`. -/
def ofJac (P : Fe C × Fe C × Fe C) : Point C :=
  if P.2.2 = 0 then .infinity else
  let zi := inv P.2.2
  .affine (P.1 * zi * zi) (P.2.1 * zi * zi * zi)

/-- The point of projective coordinates: `(X / Z, Y / Z)`, or the point at
infinity for `Z = 0`. -/
def ofProj (P : Fe C × Fe C × Fe C) : Point C :=
  if P.2.2 = 0 then .infinity else
  let zi := inv P.2.2
  .affine (P.1 * zi) (P.2.1 * zi)

/-- `-P`. -/
def neg : Point C → Point C
  | .infinity => .infinity
  | .affine x y => .affine x (-y)

/-- The points the checks take: the point at infinity, `[1]G` to `[3]G` and
their negations. -/
def points (C : Spec.Weierstrass.Curve) : List (Point C) :=
  let ms := (List.range 3).map fun i => mul (i + 1) (G C)
  .infinity :: ms ++ ms.map neg

/-- Check that `r` is `e`. -/
def expect (what : String) (r e : Point C) : Except String Unit :=
  unless r = e do throw s!"{what} is not the group law's sum"

/-- Every check on curve `C`, with the scaling factors `l₁` and `l₂` and the
doubling `dbl`; the projective additions if `proj` (`a = -3`). -/
def check (C : Spec.Weierstrass.Curve) (l₁ l₂ : Fe C)
    (dbl : Fe C → Fe C → Fe C → Fe C × Fe C × Fe C := jacDouble) (proj := true) :
    Except String Unit := do
  let b := Fin.ofNat C.p C.b
  for P in points C do
    let (X1, Y1, Z1) := toJac l₁ P
    expect "the doubling" (ofJac (dbl X1 Y1 Z1)) (add P P)
    for Q in points C do
      let (X2, Y2, Z2) := toJac l₂ Q
      let r := jacAddCached X1 Y1 Z1 X2 Y2 Z2 (Z2 * Z2) (Z2 * Z2 * Z2) dbl
      expect "jacAddCached" (ofJac r) (add P Q)
      let (U1, V1, W1) := toProj l₁ P
      let (U2, V2, W2) := toProj l₂ Q
      if proj then
        expect "rcbAdd" (ofProj (rcbAdd b U1 V1 W1 U2 V2 W2)) (add P Q)
      match Q with
      | .infinity => pure ()
      | .affine x y =>
        expect "jacAddAffine" (ofJac (jacAddAffine X1 Y1 Z1 x y 1 dbl)) (add P Q)
        let (U1, V1, W1) := toProj l₁ P
        if proj then
          expect "rcbAddAffine" (ofProj (rcbAddAffine b U1 V1 W1 x y)) (add P Q)

run_cmd do
  let result := do
    check Spec.P224.curve (Fin.ofNat _ 5) (Fin.ofNat _ 11)
    check Spec.P256.curve (Fin.ofNat _ 5) (Fin.ofNat _ 11)
    check Spec.P384.curve (Fin.ofNat _ 5) (Fin.ofNat _ 11)
    check Spec.P521.curve (Fin.ofNat _ 5) (Fin.ofNat _ 11)
    check Spec.Secp256k1.curve (Fin.ofNat _ 5) (Fin.ofNat _ 11) jacDouble0 (proj := false)
  match result with
  | .ok () => pure ()
  | .error e => throwError "PointOps: {e}"

end VG.Test.WeierstrassPointOps
