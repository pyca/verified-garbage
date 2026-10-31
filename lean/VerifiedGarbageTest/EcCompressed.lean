module

import VerifiedGarbage.Spec.EcKey.Compressed.Contract
meta import VerifiedGarbage.Spec.EcKey.Compressed.Contract
import VerifiedGarbage.Spec.P192
meta import VerifiedGarbage.Spec.P192
import VerifiedGarbage.Spec.P224
meta import VerifiedGarbage.Spec.P224
import VerifiedGarbage.Spec.P256
meta import VerifiedGarbage.Spec.P256
import VerifiedGarbage.Spec.P384
meta import VerifiedGarbage.Spec.P384
import VerifiedGarbage.Spec.P521
meta import VerifiedGarbage.Spec.P521
import VerifiedGarbage.Spec.Secp256k1
meta import VerifiedGarbage.Spec.Secp256k1
import VerifiedGarbage.Spec.BrainpoolP256r1
meta import VerifiedGarbage.Spec.BrainpoolP256r1
import VerifiedGarbage.Spec.BrainpoolP384r1
meta import VerifiedGarbage.Spec.BrainpoolP384r1
import VerifiedGarbage.Spec.BrainpoolP512r1
meta import VerifiedGarbage.Spec.BrainpoolP512r1
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms

/-!
# Checks of the compressed public-point specification

The existing curve parameters supply the base points; no new known-answer
vectors are embedded here. Exhaustive checks over a small synthetic curve
exercise the relation's bounds, tags, lengths, off-curve points and zero
root, including a field coordinate that fits in one byte but exceeds `p`.
The synthetic curve is only a test of the encoding rules, not a supported
cryptographic curve or a claim about its group order.
-/

namespace VG.Test.EcCompressed

open Spec.Weierstrass Spec.EcKey

def curves : List Curve :=
  [Spec.P192.curve, Spec.P224.curve, Spec.P256.curve, Spec.P384.curve,
    Spec.P521.curve, Spec.Secp256k1.curve, Spec.BrainpoolP256r1.curve,
    Spec.BrainpoolP384r1.curve, Spec.BrainpoolP512r1.curve]

/-- The base point and its negative both compress to validated encodings,
with opposite parity tags and unchanged `x`, for every supported curve. -/
def checkBasePoint (C : Curve) : Bool :=
  let x := Fin.ofNat C.p C.gx
  let y := Fin.ofNat C.p C.gy
  let Q : Point C := .affine x y
  let N : Point C := .affine x (-y)
  let bs := encodeCompressedPoint Q
  let ns := encodeCompressedPoint N
  decide (matchesCompressedPublicKey C bs Q) &&
    decide (matchesCompressedPublicKey C ns N) &&
    (bs.drop 1 == ns.drop 1) && (bs.head? != ns.head?) &&
    (compressPublicKey C (encodePoint Q) == some bs) &&
    (compressPublicKey C (encodePoint N) == some ns) &&
    !decide (matchesCompressedPublicKey C bs N)

#guard curves.all checkBasePoint

/-- A small field with both zero and nonzero square roots. -/
def toy : Curve where
  p := 17
  a := 1
  b := 0
  gx := 0
  gy := 0
  n := 2
  len := 1

/-- For every coordinate pair, encoding matches exactly when the point is
on the curve. Wrong tags, truncated/extended encodings and noncanonical
`x + p` never match, even though `x + p` fits in the encoding's byte. -/
def checkToyPoint (x y : Fe toy) : Bool :=
  let Q : Point toy := .affine x y
  let bs := encodeCompressedPoint Q
  (decide (matchesCompressedPublicKey toy bs Q) == onCurve toy Q) &&
    !decide (matchesCompressedPublicKey toy
      (BitVec.ofNat 8 (3 - y.val % 2) :: bs.drop 1) Q) &&
    ([0, 1, 4, 6, 7, 255] : List Byte).all (fun tag =>
      !decide (matchesCompressedPublicKey toy (tag :: bs.drop 1) Q)) &&
    !decide (matchesCompressedPublicKey toy (bs.drop 1) Q) &&
    !decide (matchesCompressedPublicKey toy (bs ++ [0]) Q) &&
    !decide (matchesCompressedPublicKey toy
      (BitVec.ofNat 8 (2 + y.val % 2) :: toBytes toy.len (x.val + toy.p)) Q)

#guard (List.finRange toy.p).all fun x => (List.finRange toy.p).all (checkToyPoint x)

/-- At every `x`, accepting some root with tag `02`/`03` is exactly the
existence of an on-curve `y` with that parity, including the zero root. -/
def checkToyRoots (x : Fe toy) : Bool :=
  ([0, 1] : List Nat).all fun parity =>
    let bs := BitVec.ofNat 8 (2 + parity) :: toBytes toy.len x.val
    let ys := List.finRange toy.p
    (ys.any fun y => decide (matchesCompressedPublicKey toy bs (.affine x y))) ==
      (ys.any fun y => onCurve toy (.affine x y) && y.val % 2 == parity)

#guard (List.finRange toy.p).all checkToyRoots
#guard matchesCompressedPublicKey toy [2, 0] (.affine 0 0)
#guard !(List.finRange toy.p).any fun y =>
  decide (matchesCompressedPublicKey toy [3, 0] (.affine 0 y))
-- At x = 2 the right-hand side is 10, a nonsquare in this test field.
#guard ([2, 3] : List Byte).all fun tag =>
  !(List.finRange toy.p).any fun y =>
    decide (matchesCompressedPublicKey toy [tag, 2] (.affine 2 y))
#guard ¬ matchesCompressedPublicKey toy [0] .infinity
#guard compressPublicKey toy [0] == none
#guard compressPublicKey toy [6, 0, 0] == none
#guard compressPublicKey toy [4, 17, 0] == none

#assert_standard_axioms VG.Spec.EcKey.encodeCompressedPoint
#assert_standard_axioms VG.Spec.EcKey.matchesCompressedPublicKey
#assert_standard_axioms VG.Spec.EcKey.compressPublicKey
#assert_standard_axioms VG.Spec.EcKey.Instance.compressPublicKeyContract
#assert_standard_axioms VG.Spec.EcKey.Instance.decompressPublicKeyContract

end VG.Test.EcCompressed
