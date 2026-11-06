module

public import VerifiedGarbage.Impl.Weierstrass.Layout.PointOps
public import VerifiedGarbage.Proof.Weierstrass.PointContract

/-!
# Point doubling and addition in a curve's working space, as internal functions

Not trusted: the formulas of five functions for a curve (`Curve`, with
`a = -3` or `a = 0`), on points kept where the x86-64 code of the curve's
ECDSA, ECDH and key derivation keeps them, so that it can call one copy of
each operation instead of repeating it at every use:

* `vg_<curve>_jac_double(ws)`: `P = 2P` in Jacobian coordinates
  (`(X : Y : Z)` for `(X / Z², Y / Z³)`), by the curve's doubling
  (`Curve.dbl`): `jacDouble`, the doubling dbl-2001-b of the
  Explicit-Formulas Database for `a = -3` with `Z₃ = 2 Y Z` as a product,
  or, for `a = 0`, `jacDouble0`, its dbl-2009-l;
* `vg_<curve>_jac_add_cached(ws)`: `P = P + Q` in Jacobian coordinates, for
  `Q` given with its `Z²` and `Z³` (which a table of points to add keeps),
  by `jacAddCached`: the addition add-1998-cmo-2, which fails for equal or
  opposite points and the point at infinity, with those cases decided by the
  coordinates (`Z = 0` for the point at infinity, `H = 0` for equal or
  opposite points) and handled as the group law does, the double of equal
  points by the curve's doubling;
* `vg_<curve>_jac_add_affine(ws)`: the same for `Q` with `Z = 1`, by
  `jacAddAffine`, the mixed addition, which does not multiply by `Q`'s `Z`;
* for a curve with `a = -3` only (no code for another curve has them),
  `vg_<curve>_proj_add_affine(ws)`: `O = P + Q` in projective coordinates
  (`(X : Y : Z)` for `(X / Z, Y / Z)`) for `Q` with `Z = 1`, by
  `rcbAddAffine`, the complete mixed addition for `a = -3` of Renes,
  Costello and Batina (*Complete addition formulas for prime order elliptic
  curves*, EUROCRYPT 2016, Algorithm 5);
  and `vg_<curve>_proj_add(ws)`: `O = P + Q` in projective coordinates, by
  `rcbAdd`, the complete addition for `a = -3` of the same paper
  (Algorithm 4), of which `rcbAddAffine` is the case `Z₂ = 1`.

They are not algorithms of a standard but the arithmetic the algorithms on
the curve are built from: what they compute is stated on the coordinates as
elements of `GF(p)`, as the functions' sequences of field operations, in
their order, whatever the points stand for. That the formulas are the group
law, for points on the curve, is a theorem of the proofs that use them
(`VerifiedGarbageTest/WeierstrassPointOps.lean` checks them against
`Spec.Weierstrass.add`).

These are internal functions (`Rust.Internal`): only verified code calls them, so
only their callers' contracts, in `Spec/`, are trusted. The structures, the
layout of the working space and the curves are the code's, in
`Impl/Weierstrass/Layout/PointOps.lean`; the definitions here are in their
namespaces, so that they read as fields of them.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.PointOps

open Mont (wsBytes)

variable {p : Nat} [NeZero p]

/-- The end of the Jacobian additions, from `U₁ = X₁ Z₂²`, `S₁ = Y₁ Z₂³`,
`H = U₂ - U₁`, `r = S₂ - S₁` (for `U₂ = X₂ Z₁²`, `S₂ = Y₂ Z₁³`) and `Z`
(`Z₁ Z₂`, or `Z₁` for `Z₂ = 1`), in the functions' order:
`X₃ = r² - H³ - 2 U₁ H²`, `Y₃ = r (U₁ H² - X₃) - S₁ H³`, `Z₃ = Z H`. -/
def jacTail (U1 S1 H r Z : Fin p) : Fin p × Fin p × Fin p :=
  let t0 := H * H
  let t1 := t0 * H
  let t2 := U1 * t0
  let X3 := r * r
  let X3 := X3 - t1
  let X3 := X3 - t2
  let X3 := X3 - t2
  let Y3 := t2 - X3
  let Y3 := r * Y3
  let t4 := S1 * t1
  let Y3 := Y3 - t4
  let Z3 := Z * H
  (X3, Y3, Z3)

/-- `H = 0`: the points are equal, and the sum is the double by `dbl` (the
curve's doubling), if `r = 0` too, else they are opposite, and the sum is
the point at infinity. -/
def jacEqual (X1 Y1 Z1 r : Fin p)
    (dbl : Fin p → Fin p → Fin p → Fin p × Fin p × Fin p := jacDouble) :
    Fin p × Fin p × Fin p :=
  if r = 0 then dbl X1 Y1 Z1 else infinity

/-- The Jacobian addition of `(X₁ : Y₁ : Z₁)` and `(X₂ : Y₂ : Z₂)` given with
`ZZ₂` and `ZZZ₂` (`Z₂²` and `Z₂³`), in the functions' order: `Q` if `P` is
the point at infinity (`Z₁ = 0`), `P` if `Q` is, else `H` and `r`, then
`jacEqual` with the doubling `dbl` if `H = 0`, else `jacTail`. -/
def jacAddCached (X1 Y1 Z1 X2 Y2 Z2 ZZ2 ZZZ2 : Fin p)
    (dbl : Fin p → Fin p → Fin p → Fin p × Fin p × Fin p := jacDouble) :
    Fin p × Fin p × Fin p :=
  if Z1 = 0 then (X2, Y2, Z2) else
  if Z2 = 0 then (X1, Y1, Z1) else
  let t0 := Z1 * Z1
  let U1 := X1 * ZZ2
  let U2 := X2 * t0
  let S1 := Y1 * ZZZ2
  let S2 := Y2 * Z1
  let S2 := S2 * t0
  let H := U2 - U1
  let r := S2 - S1
  if H = 0 then jacEqual X1 Y1 Z1 r dbl else
  let Z := Z1 * Z2
  jacTail U1 S1 H r Z

/-- The mixed Jacobian addition of `(X₁ : Y₁ : Z₁)` and `(X₂ : Y₂ : Z₂)`,
for `Z₂ = 1`, which it reads only to copy `Q` if `P` is the point at
infinity (`Z₁ = 0`), in the functions' order: else `H` and `r` (with
`U₁ = X₁`, `S₁ = Y₁`), then `jacEqual` with the doubling `dbl` if `H = 0`,
else `jacTail`. -/
def jacAddAffine (X1 Y1 Z1 X2 Y2 Z2 : Fin p)
    (dbl : Fin p → Fin p → Fin p → Fin p × Fin p × Fin p := jacDouble) :
    Fin p × Fin p × Fin p :=
  if Z1 = 0 then (X2, Y2, Z2) else
  let t0 := Z1 * Z1
  let U2 := X2 * t0
  let S2 := Y2 * Z1
  let S2 := S2 * t0
  let H := U2 - X1
  let r := S2 - Y1
  if H = 0 then jacEqual X1 Y1 Z1 r dbl else
  jacTail X1 Y1 H r Z1

/-- The complete mixed addition for `a = -3`, Algorithm 5 of Renes, Costello
and Batina, in its stated order, on the coordinates of `(X1 : Y1 : Z1)` and
`(X2 : Y2 : 1)`, for the coefficient `b`. -/
def rcbAddAffine (b X1 Y1 Z1 X2 Y2 : Fin p) : Fin p × Fin p × Fin p :=
  let t0 := X1 * X2
  let t1 := Y1 * Y2
  let t3 := X2 + Y2
  let t4 := X1 + Y1
  let t3 := t3 * t4
  let t4 := t0 + t1
  let t3 := t3 - t4
  let t4 := Y2 * Z1
  let t4 := t4 + Y1
  let Y3 := X2 * Z1
  let Y3 := Y3 + X1
  let Z3 := b * Z1
  let X3 := Y3 - Z3
  let Z3 := X3 + X3
  let X3 := X3 + Z3
  let Z3 := t1 - X3
  let X3 := t1 + X3
  let Y3 := b * Y3
  let t1 := Z1 + Z1
  let t2 := t1 + Z1
  let Y3 := Y3 - t2
  let Y3 := Y3 - t0
  let t1 := Y3 + Y3
  let Y3 := t1 + Y3
  let t1 := t0 + t0
  let t0 := t1 + t0
  let t0 := t0 - t2
  let t1 := t4 * Y3
  let t2 := t0 * Y3
  let Y3 := X3 * Z3
  let Y3 := Y3 + t2
  let X3 := t3 * X3
  let X3 := X3 - t1
  let Z3 := t4 * Z3
  let t1 := t3 * t0
  let Z3 := Z3 + t1
  (X3, Y3, Z3)

/-- The complete addition for `a = -3`, Algorithm 4 of Renes, Costello and
Batina, in its stated order, on the coordinates of `(X1 : Y1 : Z1)` and
`(X2 : Y2 : Z2)`, for the coefficient `b`. -/
def rcbAdd (b X1 Y1 Z1 X2 Y2 Z2 : Fin p) : Fin p × Fin p × Fin p :=
  let t0 := X1 * X2
  let t1 := Y1 * Y2
  let t2 := Z1 * Z2
  let t3 := X1 + Y1
  let t4 := X2 + Y2
  let t3 := t3 * t4
  let t4 := t0 + t1
  let t3 := t3 - t4
  let t4 := Y1 + Z1
  let X3 := Y2 + Z2
  let t4 := t4 * X3
  let X3 := t1 + t2
  let t4 := t4 - X3
  let X3 := X1 + Z1
  let Y3 := X2 + Z2
  let X3 := X3 * Y3
  let Y3 := t0 + t2
  let Y3 := X3 - Y3
  let Z3 := b * t2
  let X3 := Y3 - Z3
  let Z3 := X3 + X3
  let X3 := X3 + Z3
  let Z3 := t1 - X3
  let X3 := t1 + X3
  let Y3 := b * Y3
  let t1 := t2 + t2
  let t2 := t1 + t2
  let Y3 := Y3 - t2
  let Y3 := Y3 - t0
  let t1 := Y3 + Y3
  let Y3 := t1 + Y3
  let t1 := t0 + t0
  let t0 := t1 + t0
  let t0 := t0 - t2
  let t1 := t4 * Y3
  let t2 := t0 * Y3
  let Y3 := X3 * Z3
  let Y3 := Y3 + t2
  let X3 := t3 * X3
  let X3 := X3 - t1
  let Z3 := t4 * Z3
  let t1 := t3 * t0
  let Z3 := Z3 + t1
  (X3, Y3, Z3)


end VG.Impl.Weierstrass.PointOps
