module

public import VerifiedGarbageTest.Ec.Common
public meta import VerifiedGarbageTest.Ec.Common

/-!
# PEM and DER for elliptic-curve keys

Decoding the keys of vendored vector files that give them as PEM (RFC 7468):
base64 (RFC 4648 §4), DER elements, object identifiers, and the two
structures of an elliptic-curve key with named-curve parameters:

* `PrivateKeyInfo` (PKCS #8, RFC 5208 §5) of algorithm `id-ecPublicKey`,
  holding an `ECPrivateKey` (RFC 5915 §3), whose public key is optional;
* `SubjectPublicKeyInfo` (RFC 5480 §2), whose `BIT STRING` holds the point's
  octet string (SEC 1 §2.3.3).

Only what these keys use: definite lengths of at most two octets, and the
curve named by its object identifier (RFC 5480 §2.1.1's `namedCurve`).
-/

@[expose] public section

namespace VG.Test.Ec.Pem

open Spec.Weierstrass

/-! ## Base64 and PEM -/

/-- The value of a base64 character. -/
def b64 (c : Char) : Option Nat :=
  if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 'A'.toNat)
  else if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 'a'.toNat + 26)
  else if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat + 52)
  else if c == '+' then some 62 else if c == '/' then some 63 else none

/-- Base64 (RFC 4648 §4), with `=` padding. -/
def unbase64 (s : String) : Except String (List Byte) := do
  let cs := s.toList.filter (· != '=')
  let mut acc := 0
  let mut bits := 0
  let mut out : Array Byte := #[]
  for c in cs do
    let some v := b64 c | throw s!"bad base64 character {c}"
    acc := acc * 64 + v
    bits := bits + 6
    if 8 ≤ bits then
      bits := bits - 8
      out := out.push (BitVec.ofNat 8 (acc / 2 ^ bits))
      acc := acc % 2 ^ bits
  return out.toList

/-- Whether `line` begins or ends a PEM block (RFC 7468 §2). -/
def isBegin (line : String) : Bool := line.startsWith "-----BEGIN "
def isEnd (line : String) : Bool := line.startsWith "-----END "

/-! ## DER -/

/-- One DER element at the start of `bs`: its tag, its contents and what
follows it. -/
def tlv (bs : List Byte) : Except String (Nat × List Byte × List Byte) := do
  let tag :: l :: rest := bs | throw "truncated DER"
  let (len, rest) ← if l.toNat < 0x80 then pure (l.toNat, rest) else do
    let n := l.toNat - 0x80
    unless 1 ≤ n && n ≤ 2 && n ≤ rest.length do throw "bad DER length"
    pure (ofBytes (rest.take n), rest.drop n)
  unless len ≤ rest.length do throw "truncated DER"
  return (tag.toNat, rest.take len, rest.drop len)

/-- The elements of a constructed element's contents. -/
def elements (bs : List Byte) : Except String (List (Nat × List Byte)) := do
  let mut rest := bs
  let mut out := #[]
  for _ in List.range bs.length do
    if rest.isEmpty then break
    let (t, c, r) ← tlv rest
    out := out.push (t, c)
    rest := r
  return out.toList

/-- The arcs of an `OBJECT IDENTIFIER`'s contents (X.690 §8.19), whose first
two arcs are below 80 together. -/
def oid (bs : List Byte) : Except String (List Nat) := do
  let b :: rest := bs | throw "empty object identifier"
  let mut arcs : Array Nat := #[b.toNat / 40, b.toNat % 40]
  let mut acc := 0
  let mut open_ := false
  for c in rest do
    acc := acc * 128 + c.toNat % 128
    open_ := 128 ≤ c.toNat
    if !open_ then
      arcs := arcs.push acc
      acc := 0
  if open_ then throw "truncated object identifier"
  return arcs.toList

/-- The contents of a `BIT STRING` of whole octets. -/
def bitString (bs : List Byte) : Except String (List Byte) :=
  match bs with
  | b :: rest => if b.toNat == 0 then pure rest else throw "BIT STRING with unused bits"
  | [] => throw "empty BIT STRING"

/-! ## Elliptic-curve keys -/

/-- `id-ecPublicKey` (RFC 5480 §2.1.1): 1.2.840.10045.2.1. -/
def idEcPublicKey : List Nat := [1, 2, 840, 10045, 2, 1]

/-- The curve of an `AlgorithmIdentifier`'s contents: `id-ecPublicKey` with
a `namedCurve`. -/
def algorithm (bs : List Byte) : Except String (List Nat) := do
  let [(0x06, alg), (0x06, curve)] ← elements bs | throw "not an EC AlgorithmIdentifier"
  unless (← oid alg) == idEcPublicKey do throw "not id-ecPublicKey"
  oid curve

/-- An elliptic-curve private key: its curve's object identifier, the octets
of the private key, and the public key's octet string if it is given. -/
structure PrivateKey where
  curve : List Nat
  d : List Byte
  pub : Option (List Byte)

/-- A `PrivateKeyInfo` (RFC 5208 §5) holding an `ECPrivateKey`
(RFC 5915 §3), with the curve in the `AlgorithmIdentifier`. -/
def privateKey (der : List Byte) : Except String PrivateKey := do
  let (0x30, info, []) ← tlv der | throw "not a sequence"
  let [(0x02, v), (0x30, alg), (0x04, inner)] ← elements info | throw "not a PrivateKeyInfo"
  unless ofBytes v == 0 do throw "PrivateKeyInfo version"
  let curve ← algorithm alg
  let (0x30, ec, []) ← tlv inner | throw "not an ECPrivateKey"
  let (0x02, ver) :: (0x04, d) :: opt ← elements ec | throw "not an ECPrivateKey"
  unless ofBytes ver == 1 do throw "ECPrivateKey version"
  let mut pub := none
  for (t, c) in opt do
    if t == 0xa1 then
      let (0x03, bits, []) ← tlv c | throw "bad ECPrivateKey publicKey"
      pub := some (← bitString bits)
    else if t == 0xa0 then
      unless (← oid ((← tlv c).2.1)) == curve do throw "ECPrivateKey parameters"
    else throw s!"unexpected ECPrivateKey field {t}"
  return { curve, d, pub }

/-- An elliptic-curve public key: its curve's object identifier and the
point's octet string. -/
structure PublicKey where
  curve : List Nat
  point : List Byte

/-- A `SubjectPublicKeyInfo` (RFC 5480 §2). -/
def publicKey (der : List Byte) : Except String PublicKey := do
  let (0x30, info, []) ← tlv der | throw "not a sequence"
  let [(0x30, alg), (0x03, bits)] ← elements info | throw "not a SubjectPublicKeyInfo"
  return { curve := ← algorithm alg, point := ← bitString bits }

/-- The coordinates of an uncompressed point (SEC 1 §2.3.3) of `len`-octet
coordinates. -/
def uncompressed (len : Nat) (bs : List Byte) : Except String (Nat × Nat) :=
  match bs with
  | b :: rest =>
    if b.toNat == 4 && rest.length == 2 * len then
      pure (ofBytes (rest.take len), ofBytes (rest.drop len))
    else throw "not an uncompressed point"
  | [] => throw "empty point"

end VG.Test.Ec.Pem
