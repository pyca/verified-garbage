import VerifiedGarbageTest.Ec.Common
import VerifiedGarbage.Spec.Ecdsa.Verify
import VerifiedGarbage.Spec.Sha1
import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.Spec.Sha512

/-!
# ECDSA signature verification, against NIST CAVP's SigVer test

For a curve and its sections of `SigVer.rsp` (vendored byte for byte), one
with each of SHA-1, SHA-224, SHA-256, SHA-384 and SHA-512: each vector gives
a message, a public key `Q`, a signature `(R, S)` and whether it is valid
(`P`) or not (`F`, with the changed field), so they test `verify` on keys,
hashes shorter and longer than `n` and signatures that are valid and not.
The signatures whose fields are out of range, and the keys that are not
valid, are derived from the vectors and from the curve's parameters.
-/

namespace VG.Test.Ec.SigVer

open Spec.Weierstrass Spec.Ecdsa

structure Case where
  hash : String
  msg : List Byte
  qx : Nat
  qy : Nat
  r : Nat
  s : Nat
  valid : Bool

def hashes : List (String × (List Byte → List Byte)) :=
  [("SHA-1", Spec.Sha1.hash), ("SHA-224", Spec.Sha256.sha224), ("SHA-256", Spec.Sha256.hash),
    ("SHA-384", Spec.Sha512.sha384), ("SHA-512", Spec.Sha512.sha512)]

/-- The vectors of the `[name,SHA-*]` sections (`count` of them). -/
def parse (name : String) (count : Nat) (text : String) : Except String (List Case) := do
  let pre := s!"[{name},"
  let mut vs : Array Case := #[]
  let mut sect : Option String := none
  let mut cur : List (String × String) := []
  for line in lines text do
    if line.startsWith "[" then
      sect := if line.startsWith pre then
          some (String.ofList ((line.toList.drop pre.length).dropLast))
        else none
      cur := []
    else if let some h := sect then
      match line.splitOn " = " with
      | [k, v] =>
        if k == "Result" then
          let get (k : String) : Except String String := match cur.lookup k with
            | some v => pure v
            | none => throw s!"missing {k}"
          let msg ← hexBytes (← get "Msg")
          let qx ← hexNat (← get "Qx")
          let qy ← hexNat (← get "Qy")
          let r ← hexNat (← get "R")
          let sv ← hexNat (← get "S")
          vs := vs.push { hash := h, msg, qx, qy, r, s := sv, valid := v.startsWith "P" }
          cur := []
        else cur := cur ++ [(k, v)]
      | _ => pure ()
  unless vs.size == count do throw s!"expected {count} vectors, got {vs.size}"
  return vs.toList

def checkVector (C : Curve) (v : Case) : Except String Unit := do
  let pt := point C.len
  let bytes := toBytes C.len
  let some (_, H) := hashes.find? (·.1 == v.hash) | throw s!"unknown hash {v.hash}"
  let digest := H v.msg
  let e := hashToInt C digest
  let sig := bytes v.r ++ bytes v.s
  unless verify C (pt v.qx v.qy) e sig == v.valid do
    throw s!"{v.hash}, R = {v.r}: expected {v.valid}"
  -- The contract's hash argument: the leftmost `len` octets, or the hash
  -- padded on the left with zeros, which `hashToInt` reads as `e`.
  let arg := if digest.length ≥ C.len then digest.take C.len
    else List.replicate (C.len - digest.length) 0 ++ digest
  unless hashToInt C arg == e do throw s!"{v.hash}: truncated hash disagrees"
  if v.valid then
    -- Another hash, or a signature with `r` and `s` exchanged or out of
    -- range, is not valid.
    if verify C (pt v.qx v.qy) (e + 1) sig then throw "accepted another hash"
    if verify C (pt v.qx v.qy) e (bytes v.s ++ bytes v.r) then
      throw "accepted r and s exchanged"
    for (r, s) in [(0, v.s), (v.r, 0), (v.r + C.n, v.s), (v.r, v.s + C.n)] do
      if r < 2 ^ (8 * C.len) ∧ s < 2 ^ (8 * C.len) then
        if verify C (pt v.qx v.qy) e (bytes r ++ bytes s) then
          throw s!"accepted r = {r}, s = {s}"
    -- The key must be uncompressed, below `p` and on the curve.
    for pub in [0x02 :: (pt v.qx v.qy).tail, 0x00 :: (pt v.qx v.qy).tail,
        pt v.qx (v.qy + 1), pt (v.qx + C.p) v.qy, pt v.qx (C.p - v.qy)] do
      if verify C pub e sig then throw s!"accepted the key {pub}"
    -- `(x, p - y)` is `-Q`: on the curve, so only the signature fails.
    unless (Spec.EcKey.decodePublicKey C (pt v.qx (C.p - v.qy))).isSome do throw "-Q rejected"

/-- The checks of the `[name,SHA-*]` sections' `count` vectors. -/
def check (C : Curve) (name : String) (count : Nat) (text : String) : Except String Unit := do
  let vs ← parse name count text
  unless vs.any (·.valid) && vs.any (!·.valid) do
    throw "expected valid and invalid vectors"
  for v in vs do checkVector C v

end VG.Test.Ec.SigVer
