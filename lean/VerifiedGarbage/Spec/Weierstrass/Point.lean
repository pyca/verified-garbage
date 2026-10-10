import VerifiedGarbage.Spec.Weierstrass.Mont

/-!
# Complete point addition on a curve, in Montgomery form, as functions

**Trusted** (as every file in `Spec/`). The contracts of two functions for
each curve of `curves` (P-192, P-224, P-256 and P-384), so that the code of
a curve's functions can call one copy of its point addition instead of
repeating it at every use:

* `vg_<curve>_point_add(ws)`: the sum `O = P + Q` of the points at fixed
  offsets of the working space, by the complete addition formula of Renes,
  Costello and Batina (*Complete addition formulas for prime order elliptic
  curves*, EUROCRYPT 2016, Algorithm 1);
* `vg_<curve>_point_double(ws)`: the sum `O = P + P`, by the same formula.

They are not algorithms of a standard but the arithmetic every algorithm on
the curve is built from: what they compute is stated on the coordinates as
elements of `GF(p)` (`rcbAdd`, the algorithm's formulas), whatever the
points stand for. That the formula is the group law, for the curve's `a` and
`b` and points on the curve, is a theorem of the proofs that use it, not
part of these contracts.

The functions work in the representation of `Spec/Weierstrass/Mont.lean`:
a coordinate is a number of `k` 64-bit words, little-endian, below `p`, in
Montgomery's form, standing for the element `x R⁻¹` of `GF(p)`
(`R = 2^(64 k)`, `dec`). A point is three coordinates `X, Y, Z` (projective,
`(X : Y : Z)`) at consecutive offsets of the working space `ws` of 8192
bytes (`pointAt`). The points and the curve's constants are at fixed
offsets, just below the functions' own working space: the result `O`
(`oAt`), the operands `P` (`pAt`) and `Q` (`qAt`), and the curve's `a`
(`aAt`) and `3b` (`b3At`), in the same form, which the caller provides. The
functions take no offsets, so that every address they compute is `ws` plus
a constant. The bytes from `ownAt` to 4095 are the functions' own working
space: six coordinates for their intermediate values and 64 bytes to save
registers in (so that they need no stack for them), then the own working
space of the functions of `Spec/Weierstrass/Mont.lean`, which they may
call. On return they are unspecified and may hold intermediate values;
every other byte of `ws` keeps its value but the result's (`Keeps`).

Every coordinate read is below `p`, and so is the result's, so that it can
be an operand. Everything is secret but the pointer, which is public, and
the functions are constant time.

P-521 is not among the curves: its points, constants and own working space,
of nine-word coordinates, would overlap the slots its code keeps in the
working space.
-/

namespace VG.Spec.Weierstrass.Point

open Mont (wsBytes numAt)

/-- The bytes of a coordinate of `k` words. -/
def elemBytes (k : Nat) : Nat := 8 * k

/-- Where the functions' own working space starts: six coordinates and 64
bytes for saved registers below that of the functions of
`Spec/Weierstrass/Mont.lean`, which ends at byte 4096. -/
def ownAt (k : Nat) : Nat := Mont.ownAt k - 6 * elemBytes k - 64

/-- Where `3b` is: just below the own working space. -/
def b3At (k : Nat) : Nat := ownAt k - elemBytes k

/-- Where `a` is: just below `3b`. -/
def aAt (k : Nat) : Nat := b3At k - elemBytes k

/-- Where `Q` is: just below `a`. -/
def qAt (k : Nat) : Nat := aAt k - 3 * elemBytes k

/-- Where `P` is: just below `Q`. -/
def pAt (k : Nat) : Nat := qAt k - 3 * elemBytes k

/-- Where the result `O` is: just below `P`. -/
def oAt (k : Nat) : Nat := pAt k - 3 * elemBytes k

/-- Every byte of `ws` but those of the functions' own working space and of
the result keeps its value. -/
def Keeps (k : Nat) (ws : Addr) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, (i < ownAt k ∨ 4096 ≤ i) → (i < oAt k ∨ pAt k ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- The complete addition formula, Algorithm 1 of Renes, Costello and
Batina, in its stated order, on the coordinates of `(X1 : Y1 : Z1)` and
`(X2 : Y2 : Z2)`, for the coefficients `a` and `b3 = 3b`. -/
def rcbAdd {p : Nat} [NeZero p] (a b3 X1 Y1 Z1 X2 Y2 Z2 : Fin p) : Fin p × Fin p × Fin p :=
  let t0 := X1 * X2
  let t1 := Y1 * Y2
  let t2 := Z1 * Z2
  let t3 := X1 + Y1
  let t4 := X2 + Y2
  let t3 := t3 * t4
  let t4 := t0 + t1
  let t3 := t3 - t4
  let t4 := X1 + Z1
  let t5 := X2 + Z2
  let t4 := t4 * t5
  let t5 := t0 + t2
  let t4 := t4 - t5
  let t5 := Y1 + Z1
  let X3 := Y2 + Z2
  let t5 := t5 * X3
  let X3 := t1 + t2
  let t5 := t5 - X3
  let Z3 := a * t4
  let X3 := b3 * t2
  let Z3 := X3 + Z3
  let X3 := t1 - Z3
  let Z3 := t1 + Z3
  let Y3 := X3 * Z3
  let t1 := t0 + t0
  let t1 := t1 + t0
  let t2 := a * t2
  let t4 := b3 * t4
  let t1 := t1 + t2
  let t2 := t0 - t2
  let t2 := a * t2
  let t4 := t4 + t2
  let t0 := t1 * t4
  let Y3 := Y3 + t0
  let t0 := t5 * t4
  let X3 := t3 * X3
  let X3 := X3 - t0
  let t0 := t3 * t1
  let Z3 := t5 * Z3
  let Z3 := Z3 + t0
  (X3, Y3, Z3)

/-- `ws: *mut [u64; 1024]`. -/
def sig : Sig where
  params := [("ws", .array true .u64 1024)]

/-- A curve whose point addition is a function: its name (the functions are
`vg_<curve>_point_add` and `vg_<curve>_point_double`, in the Rust module
`<curve>_point`), its prime `p`, the count `k` of 64-bit words of a
coordinate, with `p < 2^(64 k)`. -/
structure Curve where
  curve : String
  p : Nat
  k : Nat
  /-- How the documentation names the curve. -/
  desc : String
  [p_ne_zero : NeZero p]

attribute [instance] Curve.p_ne_zero

namespace Curve

variable (C : Curve)

/-- `R = 2^(64 k)`. -/
def R : Nat := 2 ^ (64 * C.k)

/-- The element of `GF(p)` that the number `x` stands for in Montgomery's
form: `x R⁻¹`, with `R⁻¹ = R^(p-2)` (Fermat's little theorem, `p` prime). -/
def dec (x : Nat) : Fin C.p :=
  Fin.ofNat C.p x * Weierstrass.pow (Fin.ofNat C.p C.R) (C.p - 2)

/-- The coordinate at offset `o` of `ws`. -/
def coordAt (m : Mem) (ws : Addr) (o : Nat) : Nat := numAt m ws (BitVec.ofNat 32 o) C.k

/-- The coordinates `X, Y, Z` of the point at offset `o`, at `o`,
`o + 8 k` and `o + 16 k`. -/
def pointAt (m : Mem) (ws : Addr) (o : Nat) : Nat × Nat × Nat :=
  (C.coordAt m ws o, C.coordAt m ws (o + elemBytes C.k), C.coordAt m ws (o + 2 * elemBytes C.k))

/-- The three coordinates of a point are below `p`. -/
def Below (P : Nat × Nat × Nat) : Prop := P.1 < C.p ∧ P.2.1 < C.p ∧ P.2.2 < C.p

/-- The elements a point's coordinates stand for. -/
def decPt (P : Nat × Nat × Nat) : Fin C.p × Fin C.p × Fin C.p :=
  (C.dec P.1, C.dec P.2.1, C.dec P.2.2)

/-- The constants are below `p`. -/
def ConstsBelow (ws : Addr) (m : Mem) : Prop :=
  C.coordAt m ws (aAt C.k) < C.p ∧ C.coordAt m ws (b3At C.k) < C.p

/-- `rcbAdd` of what `a`, `3b` and the points at `p` and `q` stand for. -/
def sum (ws : Addr) (m : Mem) (p q : Nat) : Fin C.p × Fin C.p × Fin C.p :=
  let P := C.decPt (C.pointAt m ws p)
  let Q := C.decPt (C.pointAt m ws q)
  rcbAdd (C.dec (C.coordAt m ws (aAt C.k))) (C.dec (C.coordAt m ws (b3At C.k)))
    P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2

/-- What the functions require: the coordinates of the points at `p` and `q`
and the constants below `p`. -/
def sumPre (p q : Nat) (ws : Addr) (m : Mem) : Prop :=
  C.Below (C.pointAt m ws p) ∧ C.Below (C.pointAt m ws q) ∧ C.ConstsBelow ws m

/-- What they ensure: `O`'s coordinates below `p`, standing for the sum of
the points at `p` and `q`, and every byte of `ws` but `O`'s and the own
working space kept. -/
def sumPost (p q : Nat) (ws : Addr) (m m' : Mem) : Prop :=
  C.Below (C.pointAt m' ws (oAt C.k)) ∧ C.decPt (C.pointAt m' ws (oAt C.k)) = C.sum ws m p q ∧
    Keeps C.k ws m m'

/-- `add`: `O = P + Q`. -/
def addContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A (pre := fun ws m => C.sumPre (pAt C.k) (qAt C.k) ws m)
    (post := fun ws m m' _ => C.sumPost (pAt C.k) (qAt C.k) ws m m') (stack := stack)

/-- `double`: `O = P + P`. -/
def doubleContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A (pre := fun ws m => C.sumPre (pAt C.k) (pAt C.k) ws m)
    (post := fun ws m m' _ => C.sumPost (pAt C.k) (pAt C.k) ws m m') (stack := stack)

/-- The Rust module of the curve's functions. -/
def module : String := C.curve ++ "_point"

/-- The name of the function `op`. -/
def fn (op : String) : String := s!"vg_{C.curve}_point_{op}"

/-- What the documentation says of both functions. -/
def common : String :=
  s!"A point is three projective coordinates `X, Y, Z` in Montgomery's form modulo the curve's \
    prime, each {C.k} 64-bit words (`{elemBytes C.k}` bytes), little-endian, at consecutive byte \
    offsets of the working space `ws`: `O` at byte {oAt C.k}, `P` at {pAt C.k} and `Q` at \
    {qAt C.k}. The curve's `a` and `3b`, in the same form, are read at bytes {aAt C.k} and \
    {b3At C.k}. Every byte of `ws` but `O`'s and the function's own working space (bytes \
    {ownAt C.k} to 4095) keeps its value.\n\n\
    Contract: `addContract` or `doubleContract` of `VG.Spec.Weierstrass.Point.Curve`. Constant \
    time: only the pointer may affect timing."

/-- The `# Safety` items but for what the signature gives, after `reads`,
the points the function reads. -/
def safety (reads : String) : List String :=
  [s!"Every coordinate of {reads}, and the numbers at bytes {aAt C.k} and {b3At C.k}, must be \
      below {C.desc}'s prime.",
    s!"Bytes {ownAt C.k} to 4095 of `ws` are unspecified on return and may hold intermediate \
      values, which the caller must destroy if they are secret."]

/-- `vg_<curve>_point_add` on every target. -/
def addApi : Api where
  module := C.module
  name := C.fn "add"
  sig := sig
  contracts := some fun A stack => C.addContract A stack
  summary := s!"The complete addition `O = P + Q` of points on {C.desc} (Renes, Costello and \
    Batina's Algorithm 1). " ++ C.common
  safety := C.safety "the points `P` and `Q`"

/-- `vg_<curve>_point_double` on every target. -/
def doubleApi : Api where
  module := C.module
  name := C.fn "double"
  sig := sig
  contracts := some fun A stack => C.doubleContract A stack
  summary := s!"The doubling `O = P + P` of a point on {C.desc}, by the complete addition (Renes, \
    Costello and Batina's Algorithm 1). " ++ C.common
  safety := C.safety "the point `P`"

end Curve

/-! ## The curves -/

def p192 : Curve := { curve := "p192", p := Spec.P192.p, k := 3, desc := "P-192" }
def p224 : Curve := { curve := "p224", p := Spec.P224.p, k := 4, desc := "P-224" }
def p256 : Curve := { curve := "p256", p := Spec.P256.p, k := 4, desc := "P-256" }
def p384 : Curve := { curve := "p384", p := Spec.P384.p, k := 6, desc := "P-384" }

/-- Every curve. -/
def curves : List Curve := [p192, p224, p256, p384]

end VG.Spec.Weierstrass.Point
