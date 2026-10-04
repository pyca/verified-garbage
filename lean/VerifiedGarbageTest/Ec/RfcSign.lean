import VerifiedGarbageTest.Ec.Common
import VerifiedGarbage.Spec.Ecdsa
import VerifiedGarbage.Spec.Sha1
import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.Spec.Sha512

/-!
# ECDSA signing, against RFC 6979's signatures

For a curve and its section of RFC 6979's appendix A.2 (vendored byte for
byte): the key pair and the ten signatures ("sample" and "test" with SHA-1,
SHA-224, SHA-256, SHA-384 and SHA-512). Each signature is checked with the
`k` the RFC derives (`signWith` takes `k` as an input), so these test the
curve, its group law, scalar multiplication, `hashToInt` for hashes shorter
and longer than `n` and the computation of `(r, s)`. The other checks derive
their inputs from the curve's parameters.
-/

namespace VG.Test.Ec.RfcSign

open Spec.Weierstrass Spec.Ecdsa

structure Vector where
  hash : String
  message : String
  k : Nat
  r : Nat
  s : Nat

def hashes : List (String × (List Byte → List Byte)) :=
  [("SHA-1", Spec.Sha1.hash), ("SHA-224", Spec.Sha256.sha224), ("SHA-256", Spec.Sha256.hash),
    ("SHA-384", Spec.Sha512.sha384), ("SHA-512", Spec.Sha512.sha512)]

/-- The private key, the public key and the signatures of the section from
the line starting with `start` to the one starting with `stop`. -/
def parse (start stop : String) (text : String) : Except String (Nat × Nat × Nat × List Vector) := do
  let ls := joinWrapped (sectionOf text start stop)
  let x ← one ls "x"
  let ux ← one ls "Ux"
  let uy ← one ls "Uy"
  let mut vs : Array Vector := #[]
  let mut header : Option (String × String) := none
  let mut k : Option Nat := none
  let mut r : Option Nat := none
  for line in ls do
    let t := trim line
    if t.startsWith "With " then
      -- `With SHA-256, message = "sample":`
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
  return (x, ux, uy, vs.toList)

def checkVector (C : Curve) (x : Nat) (v : Vector) : Except String Unit := do
  let some (_, H) := hashes.find? (·.1 == v.hash) | throw s!"unknown hash {v.hash}"
  let digest := H (utf8 v.message)
  let e := hashToInt C digest
  unless signWith C x e v.k == some (v.r, v.s) do
    throw s!"{v.hash}, {v.message}: signature mismatch"
  let enc := encode C (v.r, v.s)
  unless enc.length == 2 * C.len && ofBytes (enc.take C.len) == v.r &&
      ofBytes (enc.drop C.len) == v.s do
    throw s!"{v.hash}, {v.message}: encoding mismatch"
  -- The contract's hash argument: the leftmost `len` octets, or the hash
  -- padded on the left with zeros, which `hashToInt` reads as `e`.
  let arg := if digest.length ≥ C.len then digest.take C.len
    else List.replicate (C.len - digest.length) 0 ++ digest
  unless hashToInt C arg == e do throw s!"{v.hash}: truncated hash disagrees"
  -- Another hash or key gives another signature.
  if signWith C x (e + 1) v.k == some (v.r, v.s) then throw "accepted another hash"
  if signWith C (x + 1) e v.k == some (v.r, v.s) then throw "accepted another key"

def checkCurve (C : Curve) (x ux uy : Nat) : Except String Unit := do
  let n := C.n
  unless onCurve C (G C) do throw "G is not on the curve"
  unless mul n (G C) == .infinity do throw "nG ≠ O"
  unless mul (n + 1) (G C) == G C do throw "(n+1)G ≠ G"
  let negG : Point C := .affine (Fin.ofNat C.p C.gx) (-(Fin.ofNat C.p C.gy))
  unless mul (n - 1) (G C) == negG do throw "(n-1)G ≠ -G"
  unless add (G C) negG == .infinity do throw "G + (-G) ≠ O"
  unless add (G C) .infinity == G C && add .infinity (G C) == G C do throw "G + O ≠ G"
  unless add (mul 2 (G C)) (G C) == mul 3 (G C) do throw "2G + G ≠ 3G"
  unless add (G C) (mul 2 (G C)) == mul 3 (G C) do throw "G + 2G ≠ 3G"
  let U := mul x (G C)
  unless U == .affine (Fin.ofNat C.p ux) (Fin.ofNat C.p uy) do throw "public key mismatch"
  unless onCurve C U && onCurve C (add U (G C)) && onCurve C (add U U) do
    throw "point not on the curve"
  -- Keys and nonces outside `[1, n-1]` give no signature.
  for (d, k) in [(0, 1), (n, 1), (n + 1, 1), (1, 0), (1, n), (1, n + 1)] do
    if (signWith C d 0 k).isSome then throw s!"signed with d = {d}, k = {k}"
  -- `hashToInt`: whole hashes up to `8 len` bits, the leftmost `8 len` bits
  -- of longer ones.
  let long := (List.range (C.len + 16)).map fun i => BitVec.ofNat 8 (i + 1)
  unless hashToInt C long == ofBytes (long.take C.len) do throw "hashToInt of a long hash"
  unless hashToInt C (long.take 20) == ofBytes (long.take 20) do throw "hashToInt of 20 octets"
  unless ofBytes (toBytes C.len ux) == ux && (toBytes C.len ux).length == C.len do
    throw "octet round trip"

/-- The checks of the section from `start` to `stop`, and of the curve. -/
def check (C : Curve) (start stop : String) (text : String) : Except String Unit := do
  let (x, ux, uy, vs) ← parse start stop text
  checkCurve C x ux uy
  for v in vs do checkVector C x v

end VG.Test.Ec.RfcSign
