module

public import VerifiedGarbage.Impl.Weierstrass.Layout.PointOps
public import VerifiedGarbage.Proof.Weierstrass.PointContract

/-!
# Point doubling and addition in a curve's working space, as internal functions

Not trusted: the contracts of five functions for
each curve of `curves` (P-224, P-256, P-384 and P-521, with `a = -3`, and
secp256k1, with `a = 0`), on points kept where the x86-64 code of the
curve's ECDSA, ECDH and key derivation keeps them, so that it can call one
copy of each operation instead of repeating it at every use:

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
law, for points on the curve, is a theorem of the proofs that use them, not
part of these contracts (`VerifiedGarbageTest/WeierstrassPointOps.lean`
checks them against `Spec.Weierstrass.add`).

The functions work in the representation of `Proof/Weierstrass/PointContract.lean`:
a coordinate is a number of `k` 64-bit words, little-endian, below `p`, in
Montgomery's form, standing for the element `x R⁻¹` of `GF(p)`
(`R = 2^(64 k)`, `Point.Curve.dec`), and a point is three coordinates at
consecutive offsets (`Point.Curve.pointAt`). The working space `ws` of 8192
bytes is the x86-64 code's: numbers of `k` words in slots from byte 64
(`slot`), where the code keeps the curve's prime `p` (slot 0, `modAt`,
which the caller provides), the accumulator `P` (slots 14 to 16, `pAt`),
the sum `O` of the projective addition (slots 17 to 19, `oAt`), the operand
`Q` (slots 20 to 22, `qAt`) and the curve's `b`, in Montgomery's form,
for the projective addition (slot 40, `bAt`); `Q`'s `Z²` and `Z³` are at
a byte offset of each curve's (`cacheAt`, `zzAt`, `zzzAt`). The functions
take no offsets, so that every address they compute is `ws` plus a
constant. Slots 17 to 19 (`O`'s, where the Jacobian functions may build
their result before copying it to `P`), 23 to 28 and the curve's temporary
slot (`tmpAt`) are the functions' own working space (`Own`); on return
they are unspecified and
may hold intermediate values. Every other byte of `ws` keeps its value but
the result's (`Keeps`).

Every coordinate read is below `p`, and so is every coordinate of the result,
so that it can be an operand. Everything is secret but the pointer, which is
public, and the doubling and the projective addition are constant time. The
Jacobian additions decide the exceptional cases by branches: their timing
may depend on the coordinates they read (`leak`), so they are only for
public points (verifying a signature).

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

/-! ## The working space -/

/-- `ws: *mut [u64; 1024]`. -/
def sig : Sig where
  params := [("ws", .array true .u64 1024)]

namespace Curve

variable (C : Curve)

/-- Byte `i` is in the functions' own working space: slots 17 to 19, 23 to
28, or the temporary slot. -/
def Own (i : Nat) : Prop :=
  (C.slot 17 ≤ i ∧ i < C.slot 20) ∨ (C.slot 23 ≤ i ∧ i < C.slot 29) ∨
    (C.tmpAt ≤ i ∧ i < C.tmpAt + 8 * C.k)

/-- Every byte of `ws` but those of the functions' own working space and of
the result, the point at `o`, keeps its value. -/
def Keeps (o : Nat) (ws : Addr) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, ¬ C.Own i → (i < o ∨ o + C.ptBytes ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- The coordinate at offset `o` is below `p`. -/
def CoordBelow (ws : Addr) (m : Mem) (o : Nat) : Prop := C.coordAt m ws o < C.p

/-- The caller provides `p` at `modAt`. -/
def ModOk (ws : Addr) (m : Mem) : Prop := C.coordAt m ws C.modAt = C.p

/-- The element the coordinate at offset `o` stands for. -/
def el (ws : Addr) (m : Mem) (o : Nat) : Fin C.p := C.dec (C.coordAt m ws o)

/-- The elements the point at offset `o` stands for. -/
def pt (ws : Addr) (m : Mem) (o : Nat) : Fin C.p × Fin C.p × Fin C.p :=
  C.decPt (C.pointAt m ws o)

/-- The result: the point at `o` has its coordinates below `p` and stands
for `r`, and every byte of `ws` but its and the own working space's keeps
its value. -/
def Result (o : Nat) (r : Fin C.p × Fin C.p × Fin C.p) (ws : Addr) (m m' : Mem) : Prop :=
  C.Below (C.pointAt m' ws o) ∧ C.pt ws m' o = r ∧ C.Keeps o ws m m'

/-- The `n` bytes of `ws` from offset `o`, as numbers. -/
def bytes (ws : Addr) (m : Mem) (o n : Nat) : List Nat :=
  (List.range n).map fun i => (m (ws + BitVec.ofNat 64 (o + i))).toNat

/-- What the Jacobian additions read, which their timing may depend on: the
bytes of `P` and `Q`, and of `Q`'s `Z²` and `Z³` if `cached`. -/
def reads (cached : Bool) (ws : Addr) (m : Mem) : List Nat :=
  bytes ws m C.pAt C.ptBytes ++ bytes ws m C.qAt C.ptBytes ++
    if cached then bytes ws m C.zzAt (16 * C.k) else []

/-- `jac_double`: `P = 2P`. -/
def doubleContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A (pre := fun ws m => C.ModOk ws m ∧ C.Below (C.pointAt m ws C.pAt))
    (post := fun ws m m' _ =>
      let P := C.pt ws m C.pAt
      C.Result C.pAt (C.dbl P.1 P.2.1 P.2.2) ws m m')
    (stack := stack)

/-- `jac_add_cached`: `P = P + Q`, `Q` with its `Z²` and `Z³`; its timing
may depend on them and on `P`. -/
def addCachedContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws m => C.ModOk ws m ∧ C.Below (C.pointAt m ws C.pAt) ∧
      C.Below (C.pointAt m ws C.qAt) ∧ C.CoordBelow ws m C.zzAt ∧ C.CoordBelow ws m C.zzzAt)
    (post := fun ws m m' _ =>
      let P := C.pt ws m C.pAt
      let Q := C.pt ws m C.qAt
      C.Result C.pAt (jacAddCached P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2 (C.el ws m C.zzAt)
        (C.el ws m C.zzzAt) C.dbl) ws m m')
    (stack := stack) (leak := some fun ws m => C.reads true ws m)

/-- `jac_add_affine`: `P = P + Q`, `Q` with `Z = 1`; its timing may depend
on `P` and `Q`. -/
def addAffineContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws m => C.ModOk ws m ∧ C.Below (C.pointAt m ws C.pAt) ∧
      C.Below (C.pointAt m ws C.qAt))
    (post := fun ws m m' _ =>
      let P := C.pt ws m C.pAt
      let Q := C.pt ws m C.qAt
      C.Result C.pAt (jacAddAffine P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2 C.dbl) ws m m')
    (stack := stack) (leak := some fun ws m => C.reads false ws m)

/-- `proj_add`: `O = P + Q`. -/
def projAddContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws m => C.ModOk ws m ∧ C.Below (C.pointAt m ws C.pAt) ∧
      C.Below (C.pointAt m ws C.qAt) ∧ C.CoordBelow ws m C.bAt)
    (post := fun ws m m' _ =>
      let P := C.pt ws m C.pAt
      let Q := C.pt ws m C.qAt
      C.Result C.oAt (rcbAdd (C.el ws m C.bAt) P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2) ws m m')
    (stack := stack)

end Curve

end VG.Impl.Weierstrass.PointOps
