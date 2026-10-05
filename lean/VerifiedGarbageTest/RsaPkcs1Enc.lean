import Lean.Elab.Command
import VerifiedGarbageTest.Sha256
import VerifiedGarbage.Spec.RsaPkcs1Enc
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-!
# RSAES-PKCS1-v1_5 with implicit rejection: known-answer tests

The test vectors of draft-irtf-cfrg-rsa-guidance-10, Appendix B, read from
the vendored draft (`vectors/draft-irtf-cfrg-rsa-guidance-10/`, see
`vectors/sources/`) when this file is built: four private keys (2048, 2049,
3072 and 4096 bits, PKCS #8 in PEM, parsed here), each with twelve
ciphertexts and the message their decryption returns: three with a valid
padding, nine with an invalid one, for which the message is the one implicit
rejection derives. No vector values are embedded in this test. For each:

* `Rsa.checkKey` accepts the key, and `decrypt` (RSADP by the CRT, checked
  against `e`: `Rsa.privateChecked`; implicit rejection keyed by the key's
  `d`, as given or with a leading zero) returns the message; the padding of
  `EM` is valid exactly for the vectors whose title says "Valid", and for
  the others the message is `alternative`.
* For a valid padding, `encrypt` with the padding string of `EM` gives the
  ciphertext back.
* A ciphertext one octet shorter or longer, and the ciphertext `n`, give
  `invalid`; a wrong `dP` gives `fault`.

The rest checks edges of the encoding layer, not known answers: `irprf`'s
output length, `altLength` at the bounds of its candidates, and
`encrypt`'s errors.
-/

namespace VG.Test.RsaPkcs1Enc

open Lean Elab Command Spec.RsaPkcs1Enc
open Spec.Rsa (os2ip i2osp)

/-! ## Base64 and DER -/

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

/-- One DER element at the start of `bs`: its tag, its contents and what
follows it. -/
def tlv (bs : List Byte) : Except String (Nat × List Byte × List Byte) := do
  let tag :: l :: rest := bs | throw "truncated DER"
  let (len, rest) ← if l.toNat < 0x80 then pure (l.toNat, rest) else do
    let n := l.toNat - 0x80
    unless 1 ≤ n && n ≤ 2 && n ≤ rest.length do throw "bad DER length"
    pure (os2ip (rest.take n), rest.drop n)
  unless len ≤ rest.length do throw "truncated DER"
  return (tag.toNat, rest.take len, rest.drop len)

/-- The elements of a DER sequence's contents. -/
def elements (bs : List Byte) : Except String (List (Nat × List Byte)) := do
  let mut rest := bs
  let mut out := #[]
  for _ in List.range bs.length do
    if rest.isEmpty then break
    let (t, c, r) ← tlv rest
    out := out.push (t, c)
    rest := r
  return out.toList

/-- A private key: `n, e, d, p, q, dP, dQ, qInv`, as integers. -/
structure Key where
  n : Nat
  e : Nat
  d : Nat
  p : Nat
  q : Nat
  dP : Nat
  dQ : Nat
  qInv : Nat

/-- A PKCS #8 `PrivateKeyInfo` (RFC 5208) holding an `RSAPrivateKey`
(RFC 8017 Appendix A.1.2) of two primes. -/
def parseKey (der : List Byte) : Except String Key := do
  let (0x30, info, []) ← tlv der | throw "not a sequence"
  let [(0x02, _), (0x30, _), (0x04, inner)] ← elements info | throw "not a PrivateKeyInfo"
  let (0x30, rsa, []) ← tlv inner | throw "not an RSAPrivateKey"
  let fields ← elements rsa
  unless fields.length == 9 && fields.all (·.1 == 0x02) do throw "not a two-prime RSAPrivateKey"
  let [v, n, e, d, p, q, dP, dQ, qInv] := fields.map (os2ip ·.2) | throw "unreachable"
  unless v == 0 do throw "version"
  return { n, e, d, p, q, dP, dQ, qInv }

/-! ## The vectors -/

/-- A test case: its title, the ciphertext and the message. -/
structure Case where
  title : String
  c : List Byte
  m : List Byte

/-- The keys of Appendix B, each with its cases. -/
structure Group where
  der : List Byte
  cases : Array Case

def isHexLine (l : String) : Bool := !l.isEmpty && l.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

def unhexE (s : String) : Except String (List Byte) := do
  let some bs := Test.Sha256.unhex s | throw s!"bad hex {s}"
  return bs

/-- Appendix B: the lines after its heading, without page footers and
headers, trimmed; a group per `-----BEGIN PRIVATE KEY-----`, a case per
`B.x.y.` heading after the key's. -/
def parse (text : String) : Except String (Array Group) := do
  let all := (text.splitOn "\n").map fun l => (String.ofList (l.toList.filter (· != '\x0c'))).trimAscii.toString
  let some start := all.findIdx? (· == "Appendix B.  Test Vectors") | throw "no Appendix B"
  let lines := (all.drop start).filter fun l =>
    !(l.startsWith "Kario " && (l.splitOn "[Page ").length > 1) &&
      !l.startsWith "Internet-Draft "
  let lines := lines.toArray
  let mut groups : Array Group := #[]
  let mut title := ""
  let mut i := 0
  -- The value (hex lines, or one ASCII line) that starts at `j`.
  let hexFrom (j : Nat) : Nat × String := Id.run do
    let mut j := j
    while j < lines.size && lines[j]!.isEmpty do j := j + 1
    let mut s := ""
    while j < lines.size && isHexLine lines[j]! do
      s := s ++ lines[j]!
      j := j + 1
    return (j, s)
  let mut c : Option (List Byte) := none
  while i < lines.size do
    let l := lines[i]!
    if l.startsWith "B." && (l.splitOn ".  ").length == 2 then
      title := (l.splitOn ".  ")[1]!
      i := i + 1
    else if l == "-----BEGIN PRIVATE KEY-----" then
      let mut b := ""
      i := i + 1
      while i < lines.size && lines[i]! != "-----END PRIVATE KEY-----" do
        b := b ++ lines[i]!
        i := i + 1
      groups := groups.push { der := ← unbase64 b, cases := #[] }
      i := i + 1
    else if l == "Hex encoded ciphertext:" then
      let (j, s) := hexFrom (i + 1)
      c := some (← unhexE s)
      i := j
    else if l.endsWith "message:" || l == "The result of decryption is a message of length 0." then
      let (j, m) ← if l == "The result of decryption is a message of length 0." then
          pure (i + 1, [])
        else if l.startsWith "Hex encoded" then do
          let (j, s) := hexFrom (i + 1)
          pure (j, ← unhexE s)
        else if l.startsWith "ASCII encoded" then do
          let mut j := i + 1
          while j < lines.size && lines[j]!.isEmpty do j := j + 1
          pure (j + 1, ascii lines[j]!)
        else throw s!"unknown message line {l}"
      let some ct := c | throw s!"message before ciphertext in {title}"
      let some g := groups.back? | throw "case before key"
      groups := groups.pop.push { g with cases := g.cases.push { title, c := ct, m } }
      c := none
      i := j
    else
      i := i + 1
  return groups

/-- Checks one key and its cases. -/
def check (g : Group) : Except String Unit := do
  let key ← parseKey g.der
  let k := (Nat.log2 key.n) / 8 + 1
  let nB := i2osp key.n k
  let eB := i2osp key.e k
  let dB := i2osp key.d k
  let pB := i2osp key.p k
  let qB := i2osp key.q k
  let dPB := i2osp key.dP k
  let dQB := i2osp key.dQ k
  let qInvB := i2osp key.qInv k
  let dec := fun (dB C : List Byte) => decrypt nB eB dB pB qB dPB dQB qInvB C
  unless Spec.Rsa.modulusValid key.n k do throw "modulus rejected"
  unless Spec.Rsa.checkKey nB eB dB pB qB dPB dQB qInvB do throw "checkKey rejected the key"
  unless g.cases.size == 12 do throw s!"{g.cases.size} cases"
  for cs in g.cases do
    unless cs.c.length == k do throw s!"{cs.title}: ciphertext of {cs.c.length} octets"
    unless dec dB cs.c == .ok cs.m do throw s!"{cs.title}: wrong message"
    -- The leading zeros of `d` do not matter.
    unless dec (0 :: dB.dropWhile (· == 0)) cs.c == .ok cs.m do
      throw s!"{cs.title}: wrong message with d of another length"
    let .ok EM := Spec.Rsa.privateChecked nB eB cs.c pB qB dPB dQB qInvB
      | throw s!"{cs.title}: RSADP failed"
    let isValid := cs.title.startsWith "Valid"
    unless valid EM == isValid do throw s!"{cs.title}: validity"
    if isValid then
      let some i := separator EM | throw "no separator"
      let PS := (EM.take i).drop 2
      unless EM == encode cs.m PS do throw s!"{cs.title}: encoding"
      unless encrypt nB eB cs.m PS == some cs.c do throw s!"{cs.title}: encryption"
    else
      unless dec dB cs.c == .ok (alternative k dB cs.c) do throw s!"{cs.title}: alternative"
    unless dec dB (cs.c.drop 1) == .invalid && dec dB (0 :: cs.c) == .invalid do
      throw s!"{cs.title}: accepted a ciphertext of another length"
  unless dec dB nB == .invalid do throw "accepted the ciphertext n"
  -- A faulty `dP`: RSADP's result fails its check against `e`.
  if let some cs := g.cases[0]? then
    unless decrypt nB eB dB pB qB (i2osp (key.dP + 2) k) dQB qInvB cs.c == .fault do
      throw "a faulty dP was not the internal error"

/-- Edges of the encoding layer. -/
def checkEdges : Except String Unit := do
  let key := List.replicate 32 (0x0b : Byte)
  for len in [0, 1, 31, 32, 33, 256, 257, 1024] do
    unless (irprf key (ascii "message") len).length == len do throw s!"irprf length {len}"
  -- A longer output starts with a shorter one only for the same `bitLength`.
  unless (irprf key (ascii "message") 64).take 32 != irprf key (ascii "message") 32 do
    throw "irprf ignores its length"
  -- All candidates `0xffff`: masked to the bit length of `k - 11`, too long
  -- unless `k - 11` is all ones.
  for (k, al) in [(64, 0), (74, 63), (256, 0), (266, 255), (1024, 0)] do
    unless altLength k (List.replicate 256 0xff) == al do throw s!"altLength {k}"
  -- The last candidate that fits is chosen, not the first.
  let cl := (List.range 128).flatMap fun i => if i < 127 then [0, BitVec.ofNat 8 i] else [0xff, 0xff]
  unless altLength 256 cl == 126 do throw "altLength picks the last fitting candidate"
  unless altLength 256 (List.replicate 256 0) == 0 do throw "altLength of zeros"
  let nB : List Byte := 0xc5 :: List.replicate 62 0xff ++ [0xfb]
  let eB : List Byte := [1, 0, 1]
  let M := List.replicate 53 (0x61 : Byte)
  unless (encrypt nB eB M (List.replicate 8 1)).isSome do throw "encrypt of 53 octets"
  unless encrypt nB eB (0 :: M) (List.replicate 7 1) == none do throw "message too long"
  unless encrypt nB eB M (List.replicate 9 1) == none do throw "PS too long"
  unless encrypt nB eB M (List.replicate 7 1 ++ [0]) == none do throw "PS with a zero"

#assert_standard_axioms Spec.RsaPkcs1Enc.encrypt
#assert_standard_axioms Spec.RsaPkcs1Enc.decrypt
#assert_no_compiler_overrides Spec.RsaPkcs1Enc.encrypt Spec.RsaPkcs1Enc.decrypt
#assert_spec_origin

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent) | throwError "no repository root"
  match checkEdges with
  | .ok () => pure ()
  | .error e => throwError "RSAES-PKCS1-v1_5 edges: {e}"
  let text ← IO.FS.readFile (root / "vectors" / "draft-irtf-cfrg-rsa-guidance-10" /
    "draft-irtf-cfrg-rsa-guidance-10.txt")
  let result : Except String Unit := do
    let groups ← parse text
    unless groups.size == 4 do throw s!"{groups.size} keys"
    for (g, i) in groups.toList.zipIdx do
      match check g with
      | .ok () => pure ()
      | .error e => throw s!"key {i + 1}: {e}"
  match result with
  | .ok () => pure ()
  | .error e => throwError "draft-irtf-cfrg-rsa-guidance-10: {e}"

end VG.Test.RsaPkcs1Enc
