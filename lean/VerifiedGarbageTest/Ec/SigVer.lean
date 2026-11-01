module

public import VerifiedGarbageTest.Ec.Common
public meta import VerifiedGarbageTest.Ec.Common
public import VerifiedGarbageTest.Memo
public meta import VerifiedGarbageTest.Memo
public import VerifiedGarbage.Spec.Ecdsa
public meta import VerifiedGarbage.Spec.Ecdsa
public import VerifiedGarbage.Spec.Ecdsa.Verify
public meta import VerifiedGarbage.Spec.Ecdsa.Verify
public import VerifiedGarbage.Spec.Sha1
public meta import VerifiedGarbage.Spec.Sha1
public import VerifiedGarbage.Spec.Sha256
public meta import VerifiedGarbage.Spec.Sha256
public import VerifiedGarbage.Spec.Sha512
public meta import VerifiedGarbage.Spec.Sha512

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

@[expose] public section

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

/-- `verifyWith`, with the multiples of `G` and of `Q` that it adds given by
`mG` and `mQ`: `verifyWith C Q` when they are `mul` (`verify_eq`), so that
the checks of a vector compute each multiple once (`Test.memo`). -/
def verifyWithM (C : Curve) (mG mQ : Nat → Point C) (e r s : Nat) : Bool :=
  if 1 ≤ r ∧ r < C.n ∧ 1 ≤ s ∧ s < C.n then
    let w : Scalar C := pow (Fin.ofNat C.n s) (C.n - 2)
    let u : Scalar C := Fin.ofNat C.n e * w
    let v : Scalar C := Fin.ofNat C.n r * w
    match add (mG u.val) (mQ v.val) with
    | .infinity => false
    | .affine x _ => x.val % C.n == r
  else false

/-- `verify`, with `verifyWithM` (`mQ (Q, v)` for `mul v Q`). -/
def verifyM (C : Curve) (mG : Nat → Point C) (mQ : Point C × Nat → Point C)
    (pub : List Byte) (e : Nat) (sig : List Byte) : Bool :=
  match Spec.EcKey.decodePublicKey C pub with
  | some Q => verifyWithM C mG (fun v => mQ (Q, v)) e (ofBytes (sig.take C.len))
      (ofBytes (sig.drop C.len))
  | none => false

theorem verify_eq (C : Curve) (pub : List Byte) (e : Nat) (sig : List Byte) :
    verify C pub e sig = verifyM C (mul · (G C)) (fun Qv => mul Qv.2 Qv.1) pub e sig :=
  rfl

/-- The scalars `u` and `v` of `G` and `Q` in `verifyWith` (for `r` and `s`
in range). -/
def scalars (C : Curve) (e r s : Nat) : Nat × Nat :=
  let w : Scalar C := pow (Fin.ofNat C.n s) (C.n - 2)
  ((Fin.ofNat C.n e * w).val, (Fin.ofNat C.n r * w).val)

def checkVector (C : Curve) (v : Case) : Except String Unit := do
  let pt := point C.len
  let bytes := toBytes C.len
  let some (_, H) := hashes.find? (·.1 == v.hash) | throw s!"unknown hash {v.hash}"
  let digest := H v.msg
  let e := hashToInt C digest
  let sig := bytes v.r ++ bytes v.s
  -- A valid vector's checks compute `uG` and `vQ` once, as `verify` with
  -- them looked up is `verify` (`verify_eq`, `Test.memo_tableOf`).
  let (u, w) := scalars C e v.r v.s
  let mulG := (mul · (G C))
  let mulQ := fun (Qv : Point C × Nat) => mul Qv.2 Qv.1
  let Q : Point C := .affine (Fin.ofNat C.p v.qx) (Fin.ofNat C.p v.qy)
  let tableG := if v.valid then Test.tableOf mulG [u] else []
  let tableQ := if v.valid then Test.tableOf mulQ [(Q, w)] else []
  let verify' := verifyM C (Test.memo tableG mulG) (Test.memo tableQ mulQ)
  unless verify' (pt v.qx v.qy) e sig == v.valid do
    throw s!"{v.hash}, R = {v.r}: expected {v.valid}"
  -- The contract's hash argument (`Ecdsa.Instance.digestDoc`): the leftmost
  -- `len` octets, or `e` shifted left by the bits `hashToInt` drops (none
  -- when `n` has `8 len` bits: the hash padded on the left with zeros).
  let arg := if digest.length ≥ C.len then digest.take C.len
    else toBytes C.len (e <<< (8 * C.len - nBits C))
  unless hashToInt C arg == e do throw s!"{v.hash}: truncated hash disagrees"
  if v.valid then
    -- Another hash, or a signature with `r` and `s` exchanged or out of
    -- range, is not valid.
    if verify' (pt v.qx v.qy) (e + 1) sig then throw "accepted another hash"
    if verify' (pt v.qx v.qy) e (bytes v.s ++ bytes v.r) then
      throw "accepted r and s exchanged"
    for (r, s) in [(0, v.s), (v.r, 0), (v.r + C.n, v.s), (v.r, v.s + C.n)] do
      if r < 2 ^ (8 * C.len) ∧ s < 2 ^ (8 * C.len) then
        if verify' (pt v.qx v.qy) e (bytes r ++ bytes s) then
          throw s!"accepted r = {r}, s = {s}"
    -- The key must be uncompressed, below `p` and on the curve.
    for pub in [0x02 :: (pt v.qx v.qy).tail, 0x00 :: (pt v.qx v.qy).tail,
        pt v.qx (v.qy + 1), pt (v.qx + C.p) v.qy, pt v.qx (C.p - v.qy)] do
      if verify' pub e sig then throw s!"accepted the key {pub}"
    -- `(x, p - y)` is `-Q`: on the curve, so only the signature fails.
    unless (Spec.EcKey.decodePublicKey C (pt v.qx (C.p - v.qy))).isSome do throw "-Q rejected"

/-- The checks of the `[name,SHA-*]` sections' `count` vectors. -/
def check (C : Curve) (name : String) (count : Nat) (text : String) : Except String Unit := do
  let vs ← parse name count text
  unless vs.any (·.valid) && vs.any (!·.valid) do
    throw "expected valid and invalid vectors"
  for v in vs do checkVector C v

end VG.Test.Ec.SigVer
