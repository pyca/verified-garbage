import VerifiedGarbage.Spec.Weierstrass.MulBase

/-!
# The contract of `Spec/Weierstrass/MulBase.lean`

* `Represents` holds for the point at infinity and for small multiples of
  P-384's base point in projective coordinates scaled by factors other than
  one, and fails for the coordinates of another point or with `Z = 0` for an
  affine point;
* the function's own working space is where the documentation says, and
  apart from what the caller provides (`p`, zero and `k`) and from the other
  tables of bits of the x86-64 code (`p - 2`'s and `n - 2`'s, from byte
  `bitsAt + 64 k + 8`).
-/

namespace VG.Test.WeierstrassMulBase

open Spec.Weierstrass Spec.Weierstrass.MulBase

/-- `Represents`, as a `Bool`. -/
def represents {W : Spec.Weierstrass.Curve} (X Y Z : Fe W) : Point W → Bool
  | .infinity => X = 0 && Y ≠ 0 && Z = 0
  | .affine x y => Z ≠ 0 && X = x * Z && Y = y * Z

theorem represents_iff {W : Spec.Weierstrass.Curve} (X Y Z : Fe W) (P : Point W) :
    represents X Y Z P = true ↔ Represents X Y Z P := by
  cases P <;> simp [represents, Represents, and_assoc]

/-- `P` in projective coordinates scaled by `l`: `(l x : l y : l)`, and
`(0 : l : 0)` for the point at infinity. -/
def toProj {W : Spec.Weierstrass.Curve} (l : Fe W) : Point W → Fe W × Fe W × Fe W
  | .infinity => (0, l, 0)
  | .affine x y => (l * x, l * y, l)

def W : Spec.Weierstrass.Curve := p384.W

def scales : List (Fe W) := [1, 2, 0x1234567, -5]

def multiples : List Nat := [0, 1, 2, 3, 7, W.n - 1, W.n]

/-- Every multiple in every scaling represents itself. -/
def checkSelf : Bool := multiples.all fun k => scales.all fun l =>
  let P := mul k (G W)
  let (X, Y, Z) := toProj l P
  represents X Y Z P

/-- No multiple's coordinates represent the next multiple, and an affine
point's coordinates with `Z = 0` represent nothing. -/
def checkOthers : Bool := multiples.all fun k => scales.all fun l =>
  let P := mul k (G W)
  let Q := mul (k + 1) (G W)
  let (X, Y, Z) := toProj l P
  !represents X Y Z Q && (match P with | .affine _ _ => !represents X Y 0 P | .infinity => true)

#guard checkSelf
#guard checkOthers

/-- Byte `i` is in the own working space, as a `Bool`. -/
def own (C : MulBase.Curve) (i : Nat) : Bool :=
  (C.slot 17 ≤ i && i < C.slot 31) || (C.slot 40 ≤ i && i < C.slot 41) ||
    (C.tmpAt ≤ i && i < C.tmpAt + 8 * C.k) || (C.bitsAt ≤ i && i < C.bitsAt + 64 * C.k + 8)

theorem own_iff (C : MulBase.Curve) (i : Nat) : own C i = true ↔ C.Own i := by
  simp [own, Curve.Own, or_assoc]

/-- The bytes of what the caller provides, and of the other tables of bits,
are not in the own working space. -/
def checkApart (C : MulBase.Curve) : Bool :=
  let words := 8 * C.k
  (List.range words).all (fun i => !own C (C.modAt + i) && !own C (C.zeroAt + i) && !own C (C.kAt + i)) &&
    (List.range (2 * (64 * C.k + 8))).all (fun i => !own C (C.bitsAt + 64 * C.k + 8 + i)) &&
    (List.range C.ptBytes).all (fun i => !own C (C.pAt + i))

#guard curves.all checkApart

#guard p384.ownDoc =
  "Bytes 880 to 1551, 1984 to 2031, 4048 to 4095 and 2224 to 2615 of `ws`"
#guard p384.kAt = 1552 ∧ p384.pAt = 736 ∧ p384.modAt = 64 ∧ p384.zeroAt = 208

end VG.Test.WeierstrassMulBase
