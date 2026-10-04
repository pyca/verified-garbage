import VerifiedGarbageTest.Ec.Common
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
import VerifiedGarbage.Spec.Sha1
import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.Spec.Sha512

/-!
# Deterministic ECDSA (RFC 6979), against the RFC's signatures

For a curve and its section of RFC 6979's appendix A.2 (vendored byte for
byte), the ten signatures ("sample" and "test" with SHA-1, SHA-224, SHA-256,
SHA-384 and SHA-512): the first candidate is the `k` the RFC lists, `sign`
gives the listed `(r, s)` after one candidate, and the contracts' instances
for the curve agree for their hashes. Keys outside `[1, n-1]`, and no
candidate to try, give no signature.
-/

namespace VG.Test.Ec.Rfc6979

open Spec.Weierstrass Spec.Ecdsa Spec.Ecdsa.Rfc6979

structure Vector where
  hash : String
  message : String
  k : Nat
  r : Nat
  s : Nat

/-- Each hash function of appendix A.2: its HMAC hash function and output
length. -/
def hashes : List (String × Spec.Hmac.HashFunction × Nat) :=
  [("SHA-1", Spec.Hmac.sha1, 20), ("SHA-224", Spec.Hmac.sha224, 28),
    ("SHA-256", Spec.Hmac.sha256, 32), ("SHA-384", Spec.Hmac.sha384, 48),
    ("SHA-512", Spec.Hmac.sha512, 64)]

/-- The private key and the signatures of the section from the line
starting with `start` to the one starting with `stop`. -/
def parse (start stop : String) (text : String) : Except String (Nat × List Vector) := do
  let ls := joinWrapped (sectionOf text start stop)
  let x ← one ls "x"
  let mut vs : Array Vector := #[]
  let mut header : Option (String × String) := none
  let mut k : Option Nat := none
  let mut r : Option Nat := none
  for line in ls do
    let t := trim line
    if t.startsWith "With " then
      match t.splitOn ", message = \"" with
      | [h, m] => header := some (String.ofList (h.toList.drop 5), (m.splitOn "\"").headD "")
      | _ => throw s!"unexpected line {t}"
    else if let some v := field "k" line then k := some (← hexNat v)
    else if let some v := field "r" line then r := some (← hexNat v)
    else if let some v := field "s" line then
      let (some (h, m), some kv, some rv) := (header, k, r) | throw "incomplete vector"
      vs := vs.push { hash := h, message := m, k := kv, r := rv, s := ← hexNat v }
      header := none; k := none; r := none
  unless vs.size == 10 do throw s!"expected 10 signatures, got {vs.size}"
  return (x, vs.toList)

/-- `insts`: the contracts' instances for the curve, by hash. -/
def checkVector (C : Curve) (insts : List (String × Spec.Ecdsa.Rfc6979.Instance)) (x : Nat) (v : Vector) :
    Except String Unit := do
  let some (_, H, hlen) := hashes.find? (·.1 == v.hash) | throw s!"unknown hash {v.hash}"
  let h1 := H.hash (utf8 v.message)
  unless h1.length == hlen do throw s!"{v.hash}: output length"
  -- The first candidate is the RFC's `k`.
  let (K, V) := init C H hlen x h1
  let (T, _) := genT H K (blocks C hlen) V
  unless bits2int C T == v.k do throw s!"{v.hash}, {v.message}: k mismatch"
  unless sign C H hlen 8 x h1 == (some (v.r, v.s), 1) do
    throw s!"{v.hash}, {v.message}: signature mismatch"
  if let some (_, I) := insts.find? (·.1 == v.hash) then
    unless I.hashLen == hlen && I.ecdsa.curve.n == C.n do throw s!"{v.hash}: instance"
    unless sign I.ecdsa.curve I.hash I.hashLen I.tries x h1 == (some (v.r, v.s), 1) do
      throw s!"{v.hash} instance, {v.message}: signature mismatch"

/-- Keys outside `[1, n-1]` give no signature and no candidate; no
candidate to try gives none. -/
def checkEdges (C : Curve) (x : Nat) : Except String Unit := do
  let H := Spec.Hmac.sha256
  let h1 := Spec.Sha256.hash (utf8 "sample")
  for d in [0, C.n, C.n + 1] do
    unless sign C H 32 8 d h1 == (none, 0) do throw s!"signed with d = {d}"
  unless sign C H 32 0 x h1 == (none, 0) do throw "signed with no candidate"
  unless rlen C == C.len do throw "rlen"

/-- The checks of the section from `start` to `stop`, with the curve's
instances `insts`. -/
def check (C : Curve) (insts : List (String × Spec.Ecdsa.Rfc6979.Instance)) (start stop : String) (text : String) :
    Except String Unit := do
  let (x, vs) ← parse start stop text
  for v in vs do checkVector C insts x v
  checkEdges C x

end VG.Test.Ec.Rfc6979
