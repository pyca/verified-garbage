import VerifiedGarbage.Spec.Weierstrass.Mont

/-!
# Complete point addition on a curve, in Montgomery form, as a function

**Trusted** (as every file in `Spec/`). The contract of one function for
each curve of `curves` (P-192, P-224, P-256 and P-384), so that the code of
a curve's functions can call one copy of its point addition instead of
repeating it at every use:

* `vg_<curve>_point_add(ws, o, p, q)`: the sum of the points at `p` and `q`
  by the complete addition formula of Renes, Costello and Batina
  (*Complete addition formulas for prime order elliptic curves*,
  EUROCRYPT 2016, Algorithm 1), written to `o`; `p` may be `q`, which
  doubles.

It is not an algorithm of a standard but the arithmetic every algorithm on
the curve is built from: what it computes is stated on the coordinates as
elements of `GF(p)` (`rcbAdd`, the algorithm's formulas), whatever the
points stand for. That the formula is the group law, for the curve's `a` and
`b` and points on the curve, is a theorem of the proofs that use it, not
part of this contract.

The function works in the representation of `Spec/Weierstrass/Mont.lean`:
a coordinate is a number of `k` 64-bit words, little-endian, below `p`, in
Montgomery's form, standing for the element `x R⁻¹` of `GF(p)`
(`R = 2^(64 k)`, `dec`). A point is three coordinates `X, Y, Z` (projective,
`(X : Y : Z)`) at consecutive offsets of the working space `ws` of 8192
bytes (`pointAt`). The offsets `o`, `p` and `q` are arguments; every point
lies below the curve's constants. The caller provides the curve's `a` and
`3b`, as coordinates, at fixed offsets below the function's own working
space (`aAt`, `b3At`), and the function only reads them. The bytes from
`ownAt` to 4095 are the function's own working space: six coordinates for
its intermediate values and 64 bytes to save registers in (so that it needs
no stack for them), then the own working space of the functions of
`Spec/Weierstrass/Mont.lean`, which it may call. On return they are
unspecified and may hold intermediate values; every other byte of `ws`
keeps its value but the result's (`Keeps`).

The result is apart from both operands, which are the same point or apart
from each other. Every coordinate is below `p`, the
result's too, so that it can be an operand. Everything is secret but the
pointer and the offsets, which are public, and the function is constant
time.

P-521 is not among the curves: its constants and own working space, of
nine-word coordinates, would overlap the slots its code keeps in the
working space.
-/

namespace VG.Spec.Weierstrass.Point

open Mont (wsBytes numAt sig)

/-- The bytes of a coordinate of `k` words. -/
def elemBytes (k : Nat) : Nat := 8 * k

/-- Where the function's own working space starts: six coordinates and 64
bytes for saved registers below that of the functions of
`Spec/Weierstrass/Mont.lean`, which ends at byte 4096. -/
def ownAt (k : Nat) : Nat := Mont.ownAt k - 6 * elemBytes k - 64

/-- Where `3b` is: just below the function's own working space. -/
def b3At (k : Nat) : Nat := ownAt k - elemBytes k

/-- Where `a` is: just below `3b`. -/
def aAt (k : Nat) : Nat := b3At k - elemBytes k

/-- The point at offset `o` lies below the constants. -/
abbrev Fits (k : Nat) (o : BitVec 32) : Prop := o.toNat + 3 * elemBytes k ≤ aAt k

/-- The points at `o` and `p` are apart. -/
abbrev Apart (k : Nat) (o p : BitVec 32) : Prop :=
  o.toNat + 3 * elemBytes k ≤ p.toNat ∨ p.toNat + 3 * elemBytes k ≤ o.toNat

/-- Every byte of `ws` but those of the function's own working space and of
the result at `o` keeps its value. -/
def Keeps (k : Nat) (ws : Addr) (o : BitVec 32) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, (i < ownAt k ∨ 4096 ≤ i) → (i < o.toNat ∨ o.toNat + 3 * elemBytes k ≤ i) →
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

/-- A curve whose point addition is a function: its name (the function is
`vg_<curve>_point_add`, in the Rust module `<curve>_point`), its prime `p`,
the count `k` of 64-bit words of a coordinate, with `p < 2^(64 k)`. -/
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
def pointAt (m : Mem) (ws : Addr) (o : BitVec 32) : Nat × Nat × Nat :=
  (C.coordAt m ws o.toNat, C.coordAt m ws (o.toNat + elemBytes C.k),
    C.coordAt m ws (o.toNat + 2 * elemBytes C.k))

/-- The three coordinates of a point are below `p`. -/
def Below (P : Nat × Nat × Nat) : Prop := P.1 < C.p ∧ P.2.1 < C.p ∧ P.2.2 < C.p

/-- The elements a point's coordinates stand for. -/
def decPt (P : Nat × Nat × Nat) : Fin C.p × Fin C.p × Fin C.p :=
  (C.dec P.1, C.dec P.2.1, C.dec P.2.2)

/-- The precondition on the offsets and the memory: the points lie below the
constants, the result apart from both operands, the operands the same or
apart, and every coordinate read, the constants' too, is below `p`. -/
def Pre (ws : Addr) (o p q : BitVec 32) (m : Mem) : Prop :=
  Fits C.k o ∧ Fits C.k p ∧ Fits C.k q ∧ Apart C.k o p ∧ Apart C.k o q ∧ (p = q ∨ Apart C.k p q) ∧
    C.Below (C.pointAt m ws p) ∧ C.Below (C.pointAt m ws q) ∧
    C.coordAt m ws (aAt C.k) < C.p ∧ C.coordAt m ws (b3At C.k) < C.p

/-- `add`: the point at `o` has coordinates below `p`, standing for
`rcbAdd` of what `a`, `3b` and the points at `p` and `q` stand for. -/
def addContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws o p q m => C.Pre ws o p q m)
    (post := fun ws o p q m m' _ =>
      C.Below (C.pointAt m' ws o) ∧
      C.decPt (C.pointAt m' ws o) =
        (let P := C.decPt (C.pointAt m ws p)
         let Q := C.decPt (C.pointAt m ws q)
         rcbAdd (C.dec (C.coordAt m ws (aAt C.k))) (C.dec (C.coordAt m ws (b3At C.k)))
           P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2) ∧
      Keeps C.k ws o m m')
    (stack := stack)

/-- The Rust module of the curve's function. -/
def module : String := C.curve ++ "_point"

/-- The function's name. -/
def fn : String := s!"vg_{C.curve}_point_add"

/-- `vg_<curve>_point_add` on every target. -/
def addApi : Api where
  module := C.module
  name := C.fn
  sig := sig
  contracts := some fun A stack => C.addContract A stack
  summary := s!"The complete addition of the points at `p` and `q` on {C.desc} (Renes, \
    Costello and Batina's Algorithm 1), written to `o`; `p` may be `q`. A point is three \
    projective coordinates `X, Y, Z` in Montgomery's form modulo the curve's prime, each {C.k} \
    64-bit words (`{elemBytes C.k}` bytes), little-endian, at consecutive byte offsets of the \
    working space `ws`. The curve's `a` and `3b`, in the same form, are read at bytes \
    {aAt C.k} and {b3At C.k} of `ws`. Every byte of `ws` but the result's and the function's \
    own working space (bytes {ownAt C.k} to 4095) keeps its value.\n\n\
    Contract: `addContract` of `VG.Spec.Weierstrass.Point.Curve`. Constant time: only the \
    pointer and the offsets may affect timing."
  safety :=
    [s!"`o`, `p` and `q` plus {3 * elemBytes C.k} must be at most {aAt C.k}: the curve's \
        constants are at bytes {aAt C.k} to {ownAt C.k - 1}, and bytes {ownAt C.k} to 4095 of \
        `ws` are the function's own working space.",
      s!"The point at `o` must be apart from those at `p` and `q`, and `p` must be `q` or the \
        points at `p` and `q` apart.",
      s!"Every coordinate of the points at `p` and `q`, and the numbers at bytes {aAt C.k} and \
        {b3At C.k}, must be below {C.desc}'s prime.",
      s!"Bytes {ownAt C.k} to 4095 of `ws` are unspecified on return and may hold intermediate \
        values, which the caller must destroy if they are secret."]

end Curve

/-! ## The curves -/

def p192 : Curve := { curve := "p192", p := Spec.P192.p, k := 3, desc := "P-192" }
def p224 : Curve := { curve := "p224", p := Spec.P224.p, k := 4, desc := "P-224" }
def p256 : Curve := { curve := "p256", p := Spec.P256.p, k := 4, desc := "P-256" }
def p384 : Curve := { curve := "p384", p := Spec.P384.p, k := 6, desc := "P-384" }

/-- Every curve. -/
def curves : List Curve := [p192, p224, p256, p384]

end VG.Spec.Weierstrass.Point
