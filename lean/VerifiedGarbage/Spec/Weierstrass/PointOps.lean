import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Spec.P521

/-!
# Point doubling and addition for `a = -3` in a curve's working space, as functions

**Trusted** (as every file in `Spec/`). The contracts of four functions for
each curve of `curves` (P-224, P-256, P-384 and P-521, all with `a = -3`),
on points kept where the x86-64 code of the curve's ECDSA, ECDH and key
derivation keeps them, so that it can call one copy of each operation
instead of repeating it at every use:

* `vg_<curve>_jac_double(ws)`: `P = 2P` in Jacobian coordinates
  (`(X : Y : Z)` for `(X / Z², Y / Z³)`), by `jacDouble`, the doubling
  dbl-2001-b of the Explicit-Formulas Database for `a = -3` with
  `Z₃ = 2 Y Z` as a product;
* `vg_<curve>_jac_add_cached(ws)`: `P = P + Q` in Jacobian coordinates, for
  `Q` given with its `Z²` and `Z³` (which a table of points to add keeps),
  by `jacAddCached`: the addition add-1998-cmo-2, which fails for equal or
  opposite points and the point at infinity, with those cases decided by the
  coordinates (`Z = 0` for the point at infinity, `H = 0` for equal or
  opposite points) and handled as the group law does;
* `vg_<curve>_jac_add_affine(ws)`: the same for `Q` with `Z = 1`, by
  `jacAddAffine`, the mixed addition, which does not multiply by `Q`'s `Z`;
* `vg_<curve>_proj_add_affine(ws)`: `O = P + Q` in projective coordinates
  (`(X : Y : Z)` for `(X / Z, Y / Z)`) for `Q` with `Z = 1`, by
  `rcbAddAffine`, the complete mixed addition for `a = -3` of Renes,
  Costello and Batina (*Complete addition formulas for prime order elliptic
  curves*, EUROCRYPT 2016, Algorithm 5).

They are not algorithms of a standard but the arithmetic the algorithms on
the curve are built from: what they compute is stated on the coordinates as
elements of `GF(p)`, as the functions' sequences of field operations, in
their order, whatever the points stand for. That the formulas are the group
law, for points on the curve, is a theorem of the proofs that use them, not
part of these contracts (`VerifiedGarbageTest/WeierstrassPointOps.lean`
checks them against `Spec.Weierstrass.add`).

The functions work in the representation of `Spec/Weierstrass/Point.lean`:
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
constant. Slots 23 to 28 and the curve's temporary slot (`tmpAt`) are the
functions' own working space (`Own`); on return they are unspecified and
may hold intermediate values. Every other byte of `ws` keeps its value but
the result's (`Keeps`).

Every coordinate read is below `p`, and so is every coordinate of the result,
so that it can be an operand. Everything is secret but the pointer, which is
public, and the doubling and the projective addition are constant time. The
Jacobian additions decide the exceptional cases by branches: their timing
may depend on the coordinates they read (`leak`), so they are only for
public points (verifying a signature).
-/

namespace VG.Spec.Weierstrass.PointOps

open Mont (wsBytes)

variable {p : Nat} [NeZero p]

/-! ## The formulas -/

/-- The point at infinity in Jacobian coordinates, as the functions write it:
`(0 : 1 : 0)`. -/
def infinity : Fin p × Fin p × Fin p := (0, 1, 0)

/-- Jacobian doubling for `a = -3` (dbl-2001-b, with `Z₃ = 2 Y Z`), in the
functions' order: `M = 3 (X - Z²)(X + Z²)`, `S = 4 X Y²`, `X₃ = M² - 2 S`,
`Y₃ = M (S - X₃) - 8 Y⁴`, `Z₃ = 2 Y Z`. -/
def jacDouble (X Y Z : Fin p) : Fin p × Fin p × Fin p :=
  let t0 := Z * Z
  let t1 := Y * Y
  let t1 := t1 + t1
  let t2 := X * t1
  let t3 := X - t0
  let X3 := X + t0
  let t3 := t3 * X3
  let X3 := t3 + t3
  let t3 := X3 + t3
  let t2 := t2 + t2
  let Z3 := Y * Z
  let Z3 := Z3 + Z3
  let X3 := t3 * t3
  let X3 := X3 - t2
  let X3 := X3 - t2
  let Y3 := t2 - X3
  let Y3 := t3 * Y3
  let t1 := t1 * t1
  let t1 := t1 + t1
  let Y3 := Y3 - t1
  (X3, Y3, Z3)

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

/-- `H = 0`: the points are equal, and the sum is the double, if `r = 0`
too, else they are opposite, and the sum is the point at infinity. -/
def jacEqual (X1 Y1 Z1 r : Fin p) : Fin p × Fin p × Fin p :=
  if r = 0 then jacDouble X1 Y1 Z1 else infinity

/-- The Jacobian addition of `(X₁ : Y₁ : Z₁)` and `(X₂ : Y₂ : Z₂)` given with
`ZZ₂` and `ZZZ₂` (`Z₂²` and `Z₂³`), in the functions' order: `Q` if `P` is
the point at infinity (`Z₁ = 0`), `P` if `Q` is, else `H` and `r`, then
`jacEqual` if `H = 0`, else `jacTail`. -/
def jacAddCached (X1 Y1 Z1 X2 Y2 Z2 ZZ2 ZZZ2 : Fin p) : Fin p × Fin p × Fin p :=
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
  if H = 0 then jacEqual X1 Y1 Z1 r else
  let Z := Z1 * Z2
  jacTail U1 S1 H r Z

/-- The mixed Jacobian addition of `(X₁ : Y₁ : Z₁)` and `(X₂ : Y₂ : Z₂)`,
for `Z₂ = 1`, which it reads only to copy `Q` if `P` is the point at
infinity (`Z₁ = 0`), in the functions' order: else `H` and `r` (with
`U₁ = X₁`, `S₁ = Y₁`), then `jacEqual` if `H = 0`, else `jacTail`. -/
def jacAddAffine (X1 Y1 Z1 X2 Y2 Z2 : Fin p) : Fin p × Fin p × Fin p :=
  if Z1 = 0 then (X2, Y2, Z2) else
  let t0 := Z1 * Z1
  let U2 := X2 * t0
  let S2 := Y2 * Z1
  let S2 := S2 * t0
  let H := U2 - X1
  let r := S2 - Y1
  if H = 0 then jacEqual X1 Y1 Z1 r else
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

/-! ## The working space -/

/-- `ws: *mut [u64; 1024]`. -/
def sig : Sig where
  params := [("ws", .array true .u64 1024)]

/-- A curve whose point operations are functions: its name, prime and words
(`Point.Curve`: the functions are `vg_<curve>_<op>`, in the Rust module
`<curve>_point_ops`), the slot of its products' temporary area, and the
byte offset of `Q`'s `Z²`, followed by its `Z³`. -/
structure Curve extends Point.Curve where
  tmp : Nat
  cache : Nat

namespace Curve

variable (C : Curve)

/-- Byte offset of slot `i`: `64 + 8 k i`. -/
def slot (i : Nat) : Nat := 64 + 8 * C.k * i

/-- Where the prime `p` is. -/
def modAt : Nat := C.slot 0

/-- Where `P` is (and the Jacobian functions' result). -/
def pAt : Nat := C.slot 14

/-- Where the projective addition's result `O` is. -/
def oAt : Nat := C.slot 17

/-- Where `Q` is. -/
def qAt : Nat := C.slot 20

/-- Where the curve's `b` is, for the projective addition. -/
def bAt : Nat := C.slot 40

/-- Where the products' temporary area is. -/
def tmpAt : Nat := C.slot C.tmp

/-- Where `Q`'s `Z²` is. -/
def zzAt : Nat := C.cache

/-- Where `Q`'s `Z³` is. -/
def zzzAt : Nat := C.cache + 8 * C.k

/-- The bytes of a point. -/
def ptBytes : Nat := 24 * C.k

/-- Byte `i` is in the functions' own working space: slots 23 to 28, or the
temporary slot. -/
def Own (i : Nat) : Prop :=
  (C.slot 23 ≤ i ∧ i < C.slot 29) ∨ (C.tmpAt ≤ i ∧ i < C.tmpAt + 8 * C.k)

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
      C.Result C.pAt (jacDouble P.1 P.2.1 P.2.2) ws m m')
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
        (C.el ws m C.zzzAt)) ws m m')
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
      C.Result C.pAt (jacAddAffine P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2) ws m m')
    (stack := stack) (leak := some fun ws m => C.reads false ws m)

/-- `proj_add_affine`: `O = P + Q`, `Q` with `Z = 1` (its `Z` is not read). -/
def projAddAffineContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws m => C.ModOk ws m ∧ C.Below (C.pointAt m ws C.pAt) ∧
      C.CoordBelow ws m C.qAt ∧ C.CoordBelow ws m (C.qAt + 8 * C.k) ∧ C.CoordBelow ws m C.bAt)
    (post := fun ws m m' _ =>
      let P := C.pt ws m C.pAt
      C.Result C.oAt (rcbAddAffine (C.el ws m C.bAt) P.1 P.2.1 P.2.2 (C.el ws m C.qAt)
        (C.el ws m (C.qAt + 8 * C.k))) ws m m')
    (stack := stack)

/-! ## The functions -/

/-- The Rust module of the curve's functions. -/
def module : String := C.curve ++ "_point_ops"

/-- The name of the function `op`. -/
def fn (op : String) : String := s!"vg_{C.curve}_{op}"

/-- Where the documentation says a point is. -/
def ptDoc (o : Nat) : String := s!"bytes {o} to {o + C.ptBytes - 1}"

/-- What the documentation says of every function. -/
def common : String :=
  s!"Coordinates are numbers of {C.k} 64-bit words (`{8 * C.k}` bytes), little-endian, in \
    Montgomery's form modulo {C.desc}'s prime `p`, and a point is three at consecutive offsets \
    of `ws`: `P` at {C.ptDoc C.pAt}, `Q` at {C.ptDoc C.qAt}. The function reads `p` at byte \
    {C.modAt}. Bytes {C.slot 23} to {C.slot 29 - 1} and {C.tmpAt} to {C.tmpAt + 8 * C.k - 1} of \
    `ws` are the function's own working space; every other byte of `ws` but the result's keeps \
    its value.\n\n\
    Contract: `doubleContract`, `addCachedContract`, `addAffineContract` or \
    `projAddAffineContract` of `VG.Spec.Weierstrass.PointOps.Curve`."

/-- The `# Safety` items but for what the signature gives, after `reads`,
the numbers the function reads besides `p`. -/
def safety (reads : String) : List String :=
  [s!"The {C.k} words at byte {C.modAt} of `ws` must be {C.desc}'s prime `p`, and {reads} must \
      be below it.",
    s!"Bytes {C.slot 23} to {C.slot 29 - 1} and {C.tmpAt} to {C.tmpAt + 8 * C.k - 1} of `ws` are \
      unspecified on return and may hold intermediate values, which the caller must destroy if \
      they are secret."]

/-- What the documentation says of the Jacobian additions' timing. -/
def leakDoc : String :=
  "Not constant time: the timing may depend on the coordinates of `P` and `Q` (and `Q`'s `Z²` and \
    `Z³`), which must be public."

/-- `vg_<curve>_jac_double` on every target. -/
def doubleApi : Api where
  module := C.module
  name := C.fn "jac_double"
  sig := sig
  contracts := some fun A stack => C.doubleContract A stack
  summary := s!"The doubling `P = 2P` of a point on {C.desc} in Jacobian coordinates, for \
    `a = -3` (dbl-2001-b, with `Z' = 2YZ`). " ++ C.common ++ " Constant time: only the pointer \
    may affect timing."
  safety := C.safety "the coordinates of `P`"

/-- `vg_<curve>_jac_add_cached` on every target. -/
def addCachedApi : Api where
  module := C.module
  name := C.fn "jac_add_cached"
  sig := sig
  contracts := some fun A stack => C.addCachedContract A stack
  summary := s!"The sum `P = P + Q` of points on {C.desc} in Jacobian coordinates, `Q` given with \
    its `Z²` at byte {C.zzAt} and `Z³` at byte {C.zzzAt} (add-1998-cmo-2, with the point at \
    infinity, equal and opposite points decided and handled). " ++ C.common ++ " " ++ leakDoc
  safety := C.safety s!"the coordinates of `P` and `Q` and the numbers at bytes {C.zzAt} and \
    {C.zzzAt}"

/-- `vg_<curve>_jac_add_affine` on every target. -/
def addAffineApi : Api where
  module := C.module
  name := C.fn "jac_add_affine"
  sig := sig
  contracts := some fun A stack => C.addAffineContract A stack
  summary := s!"The sum `P = P + Q` of points on {C.desc} in Jacobian coordinates, `Q`'s `Z` 1 \
    (the mixed addition, with the point at infinity `P`, equal and opposite points decided and \
    handled; `Q`'s `Z` is read only to copy `Q` when `P` is the point at infinity). " ++
    C.common ++ " " ++ leakDoc
  safety := C.safety "the coordinates of `P` and `Q`"

/-- `vg_<curve>_proj_add_affine` on every target. -/
def projAddAffineApi : Api where
  module := C.module
  name := C.fn "proj_add_affine"
  sig := sig
  contracts := some fun A stack => C.projAddAffineContract A stack
  summary := s!"The complete sum `O = P + Q` of points on {C.desc} in projective coordinates, \
    `Q`'s `Z` 1 and not read (Renes, Costello and Batina's Algorithm 5, for `a = -3`), into `O` \
    at {C.ptDoc C.oAt}, with the curve's `b`, in Montgomery's form, read at byte {C.bAt}. " ++
    C.common ++ " Constant time: only the pointer may affect timing."
  safety := C.safety s!"the coordinates of `P`, `Q`'s `X` and `Y` and the number at byte {C.bAt}"

end Curve

/-! ## The curves -/

def p224 : Curve := { Point.p224 with tmp := 2, cache := 5408 }
def p256 : Curve := { Point.p256 with tmp := 2, cache := 5408 }
def p384 : Curve := { Point.p384 with tmp := 83, cache := 6160 }
def p521 : Curve :=
  { curve := "p521", p := Spec.P521.p, k := 9, desc := "P-521", tmp := 55, cache := 5968 }

/-- Every curve. -/
def curves : List Curve := [p224, p256, p384, p521]

end VG.Spec.Weierstrass.PointOps
