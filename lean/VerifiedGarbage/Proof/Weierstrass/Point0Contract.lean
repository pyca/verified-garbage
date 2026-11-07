module

public import VerifiedGarbage.Proof.Weierstrass.PointContract

/-!
# Complete doubling and affine addition for `a = 0`, as internal functions

Not trusted: the formulas of two more point
functions (`Proof/Weierstrass/PointContract.lean`) for a curve `y² = x³ + b`, whose
`a` is zero (secp256k1's), by the complete formulas of Renes, Costello and
Batina for such curves (*Complete addition formulas for prime order elliptic
curves*, EUROCRYPT 2016), which take fewer products than Algorithm 1. They
are named `point_a0_…`: a name `point_double_…` or `point_add_…` would make
them variants of those functions (`ci/check_variants.py`), which they are
not.

* `vg_<curve>_point_a0_double(ws)`: `O = P + P` by Algorithm 9 (exception-free
  doubling for `a = 0`);
* `vg_<curve>_point_a0_add_affine(ws)`: `O = P + Q` by Algorithm 8 (mixed
  addition for `a = 0`), for `Q = (X₂ : Y₂ : 1)`: the function reads `Q`'s
  `X` and `Y` only.

What they compute is stated on the
coordinates as elements of `GF(p)` (`rcbDbl0`, `rcbAdd0m`: the algorithms'
formulas, in their stated order), whatever the points stand for; that the
formulas are the group law, for points on a curve with `a = 0`, is a theorem
of the proofs that use them. They read `3b` (`b3At`) and not `a`. Their
working space, offsets and representation are those of
`Proof/Weierstrass/PointContract.lean`'s functions.

These are internal functions (`Rust.Internal`): only verified code calls them, so
only their callers' contracts, in `Spec/`, are trusted. The structures, the
layout of the working space and the curves are the code's, in
`Impl/Weierstrass/Layout/Point.lean`; the definitions here are in their
namespaces, so that they read as fields of them.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.Point

/-- Algorithm 9 of Renes, Costello and Batina (doubling, `a = 0`), in its
stated order, on the coordinates of `(X : Y : Z)`, for `b3 = 3b`. -/
def rcbDbl0 {p : Nat} [NeZero p] (b3 X Y Z : Fin p) : Fin p × Fin p × Fin p :=
  let t0 := Y * Y
  let Z3 := t0 + t0
  let Z3 := Z3 + Z3
  let Z3 := Z3 + Z3
  let t1 := Y * Z
  let t2 := Z * Z
  let t2 := b3 * t2
  let X3 := t2 * Z3
  let Y3 := t0 + t2
  let Z3 := t1 * Z3
  let t1 := t2 + t2
  let t2 := t1 + t2
  let t0 := t0 - t2
  let Y3 := t0 * Y3
  let Y3 := X3 + Y3
  let t1 := X * Y
  let X3 := t0 * t1
  let X3 := X3 + X3
  (X3, Y3, Z3)

/-- Algorithm 8 of Renes, Costello and Batina (mixed addition, `a = 0`), in
its stated order, on the coordinates of `(X1 : Y1 : Z1)` and `(X2 : Y2 : 1)`,
for `b3 = 3b`. -/
def rcbAdd0m {p : Nat} [NeZero p] (b3 X1 Y1 Z1 X2 Y2 : Fin p) : Fin p × Fin p × Fin p :=
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
  let X3 := t0 + t0
  let t0 := X3 + t0
  let t2 := b3 * Z1
  let Z3 := t1 + t2
  let t1 := t1 - t2
  let Y3 := b3 * Y3
  let X3 := t4 * Y3
  let t2 := t3 * t1
  let X3 := t2 - X3
  let Y3 := Y3 * t0
  let t1 := t1 * Z3
  let Y3 := t1 + Y3
  let t0 := t0 * t3
  let Z3 := Z3 * t4
  let Z3 := Z3 + t0
  (X3, Y3, Z3)

end VG.Impl.Weierstrass.Point
