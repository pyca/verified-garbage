import Lean.Data.Json
import VerifiedGarbageTest.Ec.Cdh
import VerifiedGarbageTest.Ec.RfcSign
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
import VerifiedGarbage.Spec.Ecdsa.Verify

/-!
# Elliptic curves, against Wycheproof's ECDH and ECDSA test vectors

For a curve without CAVP or RFC vectors (secp256k1), Wycheproof's files
(vendored byte for byte):

* ECDH (`ecdh_<curve>_test.json`): each vector gives the peer's public key
  as an X.509 `SubjectPublicKeyInfo`, a private key, the shared secret and
  whether the exchange is `valid`, `acceptable` or `invalid`. Those whose key
  is the uncompressed point under the curve's own algorithm identifier (the
  others test parsing `SubjectPublicKeyInfo`, which the contracts leave to
  the caller) test `exchange`: valid vectors give their shared secret,
  invalid ones (points off the curve) none.
* ECDSA verification (`ecdsa_<curve>_<hash>_p1363_test.json`): each group
  gives a public key (`04 ‖ x ‖ y`), and each vector a message, a signature
  `r ‖ s` and whether it is valid. Those whose signature has `2 len` octets
  (the others have the wrong length, which the contracts' fixed-size
  signature rules out) test `verify`.

With the first ECDH vector's private key and its public key: the curve's
group law and keys, as for RFC 6979's (`Ec/RfcSign.lean`), and the
signatures of the curve's RFC 6979 instance, which verify with that key and
no longer once the hash changes.
-/

namespace VG.Test.Ec.Wycheproof

open Lean Spec.Weierstrass Spec.Ecdsa

def str (j : Json) (k : String) : Except String String := j.getObjValAs? String k

def arr (j : Json) (k : String) : Except String (Array Json) := do (← j.getObjVal? k).getArr?

/-- The tests of every group of a Wycheproof file, with their group. -/
def tests (text : String) : Except String (List (Json × Json)) := do
  let j ← Json.parse text
  let groups ← arr j "testGroups"
  return (← groups.toList.mapM fun g => do return (← arr g "tests").toList.map (g, ·)).flatten

/-- The ECDH checks: `valid` and `invalid` (the counts given) vectors whose
public key is `spki` followed by an uncompressed point, and of the curve.
The first valid vector's private key. -/
def checkEcdh (C : Curve) (spki : List Byte) (valid invalid : Nat) (text : String) :
    Except String Nat := do
  let mut nv := 0
  let mut ni := 0
  let mut first : Option Nat := none
  for (_, t) in ← tests text do
    let pub ← hexBytes (← str t "public")
    unless pub.take spki.length == spki ∧ pub.length == spki.length + 1 + 2 * C.len do continue
    let peer := pub.drop spki.length
    let d ← hexNat (← str t "private")
    let id ← t.getObjValAs? Nat "tcId"
    match ← str t "result" with
    | "valid" =>
      let shared ← hexBytes (← str t "shared")
      unless Spec.Ecdh.exchange C d peer == some shared do throw s!"tcId {id}: shared secret"
      if first.isNone then first := some d
      nv := nv + 1
    | "invalid" =>
      if (Spec.Ecdh.exchange C d peer).isSome then throw s!"tcId {id}: accepted"
      if (Spec.EcKey.decodePublicKey C peer).isSome then throw s!"tcId {id}: decoded"
      ni := ni + 1
    | _ => pure ()
  unless nv == valid ∧ ni == invalid do throw s!"{nv} valid and {ni} invalid vectors"
  Cdh.checkCurve C
  let some d := first | throw "no valid vector"
  return d

/-- The ECDSA verification checks: the `valid` and `invalid` (the counts
given) vectors whose signature has `2 len` octets, with the hash `H`. -/
def checkVerify (C : Curve) (H : List Byte → List Byte) (valid invalid : Nat) (text : String) :
    Except String Unit := do
  let mut nv := 0
  let mut ni := 0
  for (g, t) in ← tests text do
    let pub ← hexBytes (← str (← g.getObjVal? "publicKey") "uncompressed")
    let sig ← hexBytes (← str t "sig")
    unless sig.length == 2 * C.len do continue
    let e := hashToInt C (H (← hexBytes (← str t "msg")))
    let id ← t.getObjValAs? Nat "tcId"
    match ← str t "result" with
    | "valid" =>
      unless verify C pub e sig do throw s!"tcId {id}: rejected"
      if verify C pub (e + 1) sig then throw s!"tcId {id}: accepted another hash"
      nv := nv + 1
    | "invalid" =>
      if verify C pub e sig then throw s!"tcId {id}: accepted"
      ni := ni + 1
    | r => throw s!"tcId {id}: result {r}"
  unless nv == valid ∧ ni == invalid do throw s!"{nv} valid and {ni} invalid vectors"

/-- The group law and keys with the private key `d`, and the signatures of
the curve's RFC 6979 instance `I` with it. -/
def checkSign (C : Curve) (I : Rfc6979.Instance) (d : Nat) : Except String Unit := do
  let .affine x y := mul d (G C) | throw "dG = O"
  RfcSign.checkCurve C d x.val y.val
  unless I.ecdsa.curve.n == C.n && I.ecdsa.curve.len == C.len do throw "instance"
  let pub := point C.len x.val y.val
  for m in ["sample", "test"] do
    let h1 := I.hash.hash (utf8 m)
    unless h1.length == I.hashLen do throw "hash length"
    let (some (r, s), tries) := Rfc6979.sign C I.hash I.hashLen I.tries d h1
      | throw s!"{m}: no signature"
    unless 1 ≤ tries ∧ tries ≤ I.tries do throw s!"{m}: {tries} candidates"
    let e := hashToInt C h1
    let sig := toBytes C.len r ++ toBytes C.len s
    unless verify C pub e sig do throw s!"{m}: signature does not verify"
    if verify C pub (e + 1) sig then throw s!"{m}: verified another hash"

end VG.Test.Ec.Wycheproof
