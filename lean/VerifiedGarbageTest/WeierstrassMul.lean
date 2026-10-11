import VerifiedGarbage.Spec.Weierstrass.Mul

/-!
# The contract of `Spec/Weierstrass/Mul.lean`

* the function's own working space is where the documentation says, and
  apart from what the caller provides (`p`, zero, the constants, `Q` and
  `k`), from the result, and from the other tables of bits of the x86-64
  code (`p - 2`'s and `n - 2`'s, from byte `bitsAt + 64 k + 8`);
* each curve's base point satisfies `PointOk` in Montgomery's form, and the
  constants `ConstsOk` asks for are the curve's.
-/

namespace VG.Test.WeierstrassMul

open Spec.Weierstrass Spec.Weierstrass.Mul

/-- Byte `i` is in the own working space, as a `Bool`. -/
def own (C : Mul.Curve) (i : Nat) : Bool :=
  (C.slot 17 ≤ i && i < C.slot 31) || (C.tmpAt ≤ i && i < C.tmpAt + 8 * C.k) ||
    (C.bitsAt ≤ i && i < C.bitsAt + 64 * C.k + 8)

theorem own_iff (C : Mul.Curve) (i : Nat) : own C i = true ↔ C.Own i := by
  simp [own, Curve.Own, or_assoc]

/-- The bytes of what the caller provides, of the result and of the other
tables of bits are not in the own working space. -/
def checkApart (C : Mul.Curve) : Bool :=
  let words := 8 * C.k
  (List.range words).all (fun i => [C.modAt, C.zeroAt, C.oneAt, C.aAt, C.b3At, C.qAt, C.qAt + words,
      C.kAt].all fun o => !own C (o + i)) &&
    (List.range (2 * (64 * C.k + 8))).all (fun i => !own C (C.bitsAt + 64 * C.k + 8 + i)) &&
    (List.range C.ptBytes).all (fun i => !own C (C.pAt + i))

#guard curves.all checkApart

/-- What the caller provides and the result do not overlap: their slots are
distinct, each of `k` words. -/
def checkInputs (C : Mul.Curve) : Bool :=
  let os := [C.modAt, C.zeroAt, C.oneAt, C.aAt, C.b3At, C.qAt, C.qAt + 8 * C.k, C.kAt, C.pAt,
    C.pAt + 8 * C.k, C.pAt + 16 * C.k]
  os.all fun o => os.all fun o' => o = o' || o + 8 * C.k ≤ o' || o' + 8 * C.k ≤ o

#guard curves.all checkInputs

#guard [p192, secp256k1].all fun C =>
  C.ownDoc == "Bytes 608 to 1055, 128 to 159 and 1504 to 1767 of `ws`" &&
    C.kAt == 1056 && C.pAt == 512 && C.modAt == 64 && C.zeroAt == 160 && C.oneAt == 224 &&
    C.aAt == 256 && C.b3At == 288 && C.qAt == 320

/-- The base point in Montgomery's form is a point `PointOk` accepts: its
coordinates below `p`, and decoding them gives `G` on the curve. -/
def checkG (C : Mul.Curve) : Bool :=
  let x := C.mont C.W.gx
  let y := C.mont C.W.gy
  x < C.W.p && y < C.W.p && (C.toPoint.dec x).val == C.W.gx % C.W.p &&
    (C.toPoint.dec y).val == C.W.gy % C.W.p && onCurve C.W (G C.W)

#guard curves.all checkG

/-- The constants decode to one, `a` and `3 b`. -/
def checkConsts (C : Mul.Curve) : Bool :=
  (C.toPoint.dec (C.mont 1)).val == 1 && (C.toPoint.dec (C.mont C.W.a)).val == C.W.a % C.W.p &&
    (C.toPoint.dec (C.mont (3 * C.W.b))).val == 3 * C.W.b % C.W.p

#guard curves.all checkConsts

end VG.Test.WeierstrassMul
