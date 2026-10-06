import VerifiedGarbageTest.Ec.Cdh
import VerifiedGarbageTest.Ec.RfcSign
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
import VerifiedGarbage.Spec.Ecdsa.Verify
import VerifiedGarbage.Spec.Sha256

/-!
# Elliptic curves without published test vectors

For a curve that neither CAVP nor an RFC has vectors for (secp256k1), checks
that the specification is consistent with itself and with the curve's
parameters, with private keys derived from labels by SHA-256 (the Rust tests
run Wycheproof's vectors against the implementation):

* the group law and keys, as for RFC 6979's (`Ec/RfcSign.lean`): `G` on the
  curve, `[n]G = O`, `[n - 1]G = -G`, and small multiples;
* ECDH (`checkEcdh`): both sides of an exchange, and the shared point by a
  third path, `[a b mod n]G`, with the checks of a CAVP vector
  (`Ec/Cdh.lean`, including invalid public and private keys);
* ECDSA (`checkSign`): the signatures of the curve's RFC 6979 instance,
  which verify with the signer's public key, and no longer once the hash,
  the signature or the key changes.
-/

namespace VG.Test.Ec.SelfCheck

open Spec.Weierstrass Spec.Ecdsa

/-- A private key in `[1, n - 1]` from `label`: its SHA-256 hash modulo `n - 1`, plus 1. -/
def key (C : Curve) (label : String) : Nat := ofBytes (Spec.Sha256.hash (utf8 label)) % (C.n - 1) + 1

/-- The affine coordinates of `[d]G`. -/
def pub (C : Curve) (d : Nat) : Except String (Nat × Nat) :=
  match mul d (G C) with
  | .affine x y => pure (x.val, y.val)
  | .infinity => throw s!"[{d}]G = O"

/-- The ECDH checks with the private keys `a` and `b`, and of the curve. -/
def checkEcdh (C : Curve) (a b : Nat) : Except String Unit := do
  let (xa, ya) ← pub C a
  let (xb, yb) ← pub C b
  let (z, _) ← pub C (a * b % C.n)
  Cdh.checkVector C 0 { qx := xb, qy := yb, d := a, ux := xa, uy := ya, z }
  Cdh.checkVector C 1 { qx := xa, qy := ya, d := b, ux := xb, uy := yb, z }
  Cdh.checkCurve C

/-- The group law and keys with the private key `d`, and the signatures of
the curve's RFC 6979 instance `I` with it, checked with the public key of
`d` and of `d'`. -/
def checkSign (C : Curve) (I : Rfc6979.Instance) (d d' : Nat) : Except String Unit := do
  let (x, y) ← pub C d
  RfcSign.checkCurve C d x y
  unless I.ecdsa.curve.n == C.n && I.ecdsa.curve.len == C.len do throw "instance"
  let q := point C.len x y
  let (x', y') ← pub C d'
  for m in ["sample", "test"] do
    let h1 := I.hash.hash (utf8 m)
    unless h1.length == I.hashLen do throw "hash length"
    let (some (r, s), tries) := Rfc6979.sign C I.hash I.hashLen I.tries d h1
      | throw s!"{m}: no signature"
    unless 1 ≤ tries ∧ tries ≤ I.tries do throw s!"{m}: {tries} candidates"
    let e := hashToInt C h1
    let sig := toBytes C.len r ++ toBytes C.len s
    unless verify C q e sig do throw s!"{m}: signature does not verify"
    if verify C q (e + 1) sig then throw s!"{m}: verified another hash"
    if verify C q e (toBytes C.len r ++ toBytes C.len ((s + 1) % C.n)) then
      throw s!"{m}: verified another signature"
    if verify C (point C.len x' y') e sig then throw s!"{m}: verified with another key"

end VG.Test.Ec.SelfCheck
