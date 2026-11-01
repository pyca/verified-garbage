module

public import VerifiedGarbage.Impl.Weierstrass.Layout.Point

/-!
# Point doubling and addition in a curve's working space: its curves and offsets, and the doublings

Not trusted: what the code of the curves' internal functions (`Rust.Internal`),
which only verified code calls, is generated from, and where it keeps its
numbers. Their contracts are in `Proof/Weierstrass/PointOpsContract.lean`, in these
namespaces.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.PointOps

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

/-- Jacobian doubling for `a = 0` (dbl-2009-l, with `Z₃ = 2 Y Z`), in the
functions' order: `A = X²`, `B = Y²`, `C = B²`, `D = 2 ((X + B)² - A - C)`,
`E = 3 A`, `Z₃ = 2 Y Z`, `X₃ = E² - 2 D`, `Y₃ = E (D - X₃) - 8 C`. -/
def jacDouble0 (X Y Z : Fin p) : Fin p × Fin p × Fin p :=
  let t0 := X * X
  let t1 := Y * Y
  let t2 := t1 * t1
  let t3 := X + t1
  let t3 := t3 * t3
  let t3 := t3 - t0
  let t3 := t3 - t2
  let t3 := t3 + t3
  let t4 := t0 + t0
  let t4 := t4 + t0
  let Z3 := Y * Z
  let Z3 := Z3 + Z3
  let X3 := t4 * t4
  let X3 := X3 - t3
  let X3 := X3 - t3
  let Y3 := t3 - X3
  let Y3 := t4 * Y3
  let t2 := t2 + t2
  let t2 := t2 + t2
  let t2 := t2 + t2
  let Y3 := Y3 - t2
  (X3, Y3, Z3)

/-- A curve whose point operations are functions: its name, prime and words
(`Point.Curve`: the functions are `vg_<curve>_<op>`, in the Rust module
`<curve>_point_ops`), the slot of its products' temporary area, the
byte offset of `Q`'s `Z²`, followed by its `Z³`, and its Jacobian doubling,
which the doubling and the additions of equal points compute: `jacDouble`
for a curve with `a = -3` (the default), `jacDouble0` for one with
`a = 0`, with `dblDoc` naming it. -/
structure Curve extends Point.Curve where
  tmp : Nat
  cache : Nat
  dbl : Fin p → Fin p → Fin p → Fin p × Fin p × Fin p := jacDouble
  dblDoc : String := "for `a = -3` (dbl-2001-b, with `Z' = 2YZ`)"

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

/-- The name of the function `op`. -/
def fn (op : String) : String := s!"vg_{C.curve}_{op}"

end Curve

/-! ## The curves -/

def p224 : Curve := { Point.p224 with tmp := 2, cache := 5408 }

def p256 : Curve := { Point.p256 with tmp := 2, cache := 5408 }

def p384 : Curve := { Point.p384 with tmp := 83, cache := 6160 }

def p521 : Curve :=
  { curve := "p521", p := Spec.P521.p, k := 9, desc := "P-521", tmp := 55, cache := 5968 }

def secp256k1 : Curve :=
  { curve := "secp256k1", p := Spec.Secp256k1.p, k := 4, desc := "secp256k1", tmp := 2,
    cache := 5408, dbl := jacDouble0, dblDoc := "for `a = 0` (dbl-2009-l, with `Z' = 2YZ`)" }

/-- Every curve. -/
def curves : List Curve := [p224, p256, p384, p521, secp256k1]

end VG.Impl.Weierstrass.PointOps
