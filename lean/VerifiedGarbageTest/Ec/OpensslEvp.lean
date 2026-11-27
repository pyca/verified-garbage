module

public import VerifiedGarbageTest.Ec.Pem
public meta import VerifiedGarbageTest.Ec.Pem
public import VerifiedGarbageTest.Ec.Cdh
public meta import VerifiedGarbageTest.Ec.Cdh

/-!
# Elliptic-curve keys and ECDH, against OpenSSL's EVP test files

OpenSSL's `test/recipes/30-test_evp_data/evppkey_*.txt` (vendored byte for
byte) are stanzas of `Keyword = value` lines, separated by blank lines;
`#` starts a comment. The ones read here:

* `PrivateKey = NAME` or `PublicKey = NAME`, followed by the key as PEM
  (`Ec/Pem.lean`);
* `PrivPubKeyPair = PRIV:PUB`: the public key of `PRIV` is `PUB`;
* `Derive = PRIV`, `PeerKey = PUB` and `SharedSecret = HEX`: ECDH of `PRIV`
  with `PUB` gives `HEX`.

For two key pairs, both exchanges are checked as a CAVP ECC CDH vector
(`Ec/Cdh.lean`, with its invalid public and private keys).
-/

@[expose] public section

namespace VG.Test.Ec.OpensslEvp

open Spec.Weierstrass

/-- `s` without the spaces at either end. -/
def strip (s : String) : String :=
  String.ofList ((s.toList.dropWhile (· == ' ')).reverse.dropWhile (· == ' ')).reverse

/-- A stanza: its `Keyword = value` lines, and the DER of its PEM block if it
has one. -/
structure Stanza where
  fields : List (String × String)
  der : Option (List Byte)

/-- The stanzas of the file. -/
def stanzas (text : String) : Except String (List Stanza) := do
  let mut out : Array Stanza := #[]
  let mut fields : Array (String × String) := #[]
  let mut der : Option (List Byte) := none
  let mut body : Option String := none
  for line in lines text ++ [""] do
    if let some b := body then
      if Pem.isEnd line then
        der := some (← Pem.unbase64 b)
        body := none
      else body := some (b ++ strip line)
    else if Pem.isBegin line then body := some ""
    else if strip line == "" then
      unless fields.isEmpty do out := out.push { fields := fields.toList, der }
      fields := #[]
      der := none
    else if !line.startsWith "#" then
      match line.splitOn "=" with
      | k :: v => fields := fields.push (strip k, strip ("=".intercalate v))
      | [] => pure ()
  if body.isSome then throw "unterminated PEM block"
  return out.toList

/-- The DER of the key `name` (`kind` is `PrivateKey` or `PublicKey`). -/
def key (ss : List Stanza) (kind name : String) : Except String (List Byte) :=
  match ss.find? (·.fields.lookup kind == some name) with
  | some { der := some d, .. } => pure d
  | _ => throw s!"no {kind} {name}"

/-- The value of `field` in the stanza holding every one of `fields`. -/
def lookup (ss : List Stanza) (fields : List (String × String)) (field : String) :
    Except String String :=
  match ss.find? (fun s => fields.all (s.fields.contains ·)) with
  | some s => match s.fields.lookup field with
    | some v => pure v
    | none => throw s!"no {field} for {fields}"
  | none => throw s!"no stanza {fields}"

/-- The ECDH checks of the key pairs `a` and `b` (whose public keys are
`a_PUB` and `b_PUB`) of the curve `C`, named by the object identifier
`curveOid` in the keys. -/
def checkEcdh (C : Curve) (curveOid : List Nat) (a b : String) (text : String) :
    Except String Unit := do
  let ss ← stanzas text
  let side (n : String) : Except String (Nat × Nat × Nat) := do
    let d ← Pem.privateKey (← key ss "PrivateKey" n)
    let q ← Pem.publicKey (← key ss "PublicKey" (n ++ "_PUB"))
    unless d.curve == curveOid && q.curve == curveOid do throw s!"{n}: not the curve's object identifier"
    unless d.d.length == C.len do throw s!"{n}: private key of {d.d.length} octets"
    if let some p := d.pub then
      unless p == q.point do throw s!"{n}: the private key's public key is not {n}_PUB"
    let (x, y) ← Pem.uncompressed C.len q.point
    -- The file states that `n_PUB` is the public key of `n`; `Cdh.checkVector` checks it.
    unless ss.any (·.fields.contains ("PrivPubKeyPair", s!"{n}:{n}_PUB")) do
      throw s!"{n}: no PrivPubKeyPair"
    return (ofBytes d.d, x, y)
  let (da, xa, ya) ← side a
  let (db, xb, yb) ← side b
  let secret (n peer : String) : Except String (List Byte) := do
    hexBytes (← lookup ss [("Derive", n), ("PeerKey", peer ++ "_PUB")] "SharedSecret")
  let zab ← secret a b
  let zba ← secret b a
  unless zab.length == C.len && zab == zba do throw "shared secrets"
  Cdh.checkVector C 0 { qx := xb, qy := yb, d := da, ux := xa, uy := ya, z := ofBytes zab }
  Cdh.checkVector C 1 { qx := xa, qy := ya, d := db, ux := xb, uy := yb, z := ofBytes zba }

end VG.Test.Ec.OpensslEvp
