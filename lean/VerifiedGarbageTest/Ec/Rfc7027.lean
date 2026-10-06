import VerifiedGarbageTest.Ec.Cdh
import VerifiedGarbageTest.Ec.RfcSign
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
import VerifiedGarbage.Spec.Ecdsa.Verify

/-!
# Brainpool curves, against RFC 7027's ECDH test vectors

For a curve and its section of RFC 7027's appendix A (vendored byte for
byte): two key pairs `(dA, qA)` and `(dB, qB)` and their shared point `Z`.
Each side's exchange is checked as a CAVP ECC CDH vector (`Ec/Cdh.lean`),
and the shared point's `y` too. With the first key pair: the curve's group
law and keys, as for RFC 6979's (`Ec/RfcSign.lean`); and the signatures of
the curve's RFC 6979 instance, which verify with its public key, and no
longer once the hash or the key changes.
-/

namespace VG.Test.Ec.Rfc7027

open Spec.Weierstrass Spec.Ecdsa

/-- The values of the section from the line starting with `start` to the
one starting with `stop`: `name = HEX` lines, the hexadecimal digits of
each continuing on the lines after it (between the pages' headers). -/
def parse (start stop : String) (text : String) : Except String (List (String × Nat)) := do
  let mut cur : Option (String × String) := none
  let mut vals : Array (String × Nat) := #[]
  for line in sectionOf text start stop do
    let t := trim line
    match t.splitOn " =" with
    | [k, v] =>
      if let some (k', v') := cur then vals := vals.push (k', ← hexNat v')
      cur := some (k, trim v)
    | _ =>
      if !t.isEmpty && t.all (hexDigit · |>.isSome) then
        if let some (k, v) := cur then cur := some (k, v ++ t)
  if let some (k, v) := cur then vals := vals.push (k, ← hexNat v)
  return vals.toList

def get (vals : List (String × Nat)) (k : String) : Except String Nat :=
  match vals.lookup k with
  | some v => pure v
  | none => throw s!"missing {k}"

/-- The ECDH checks of the section from `start` to `stop`. -/
def checkEcdh (C : Curve) (start stop : String) (text : String) : Except String Unit := do
  let vals ← parse start stop text
  let g := get vals
  let (dA, xA, yA, dB, xB, yB, xZ, yZ) :=
    (← g "dA", ← g "x_qA", ← g "y_qA", ← g "dB", ← g "x_qB", ← g "y_qB", ← g "x_Z", ← g "y_Z")
  Cdh.checkVector C 0 { qx := xB, qy := yB, d := dA, ux := xA, uy := yA, z := xZ }
  Cdh.checkVector C 1 { qx := xA, qy := yA, d := dB, ux := xB, uy := yB, z := xZ }
  let Z : Point C := .affine (Fin.ofNat C.p xZ) (Fin.ofNat C.p yZ)
  unless mul dA (.affine (Fin.ofNat C.p xB) (Fin.ofNat C.p yB)) == Z do throw "dA qB ≠ Z"
  unless mul dB (.affine (Fin.ofNat C.p xA) (Fin.ofNat C.p yA)) == Z do throw "dB qA ≠ Z"
  Cdh.checkCurve C

/-- The ECDSA checks of the section from `start` to `stop`, for the curve's
RFC 6979 instance `I`. -/
def checkEcdsa (C : Curve) (I : Rfc6979.Instance) (start stop : String) (text : String) :
    Except String Unit := do
  let vals ← parse start stop text
  let g := get vals
  let (d, x, y, xB, yB) := (← g "dA", ← g "x_qA", ← g "y_qA", ← g "x_qB", ← g "y_qB")
  RfcSign.checkCurve C d x y
  unless I.ecdsa.curve.n == C.n && I.ecdsa.curve.len == C.len do throw "instance"
  let pub := point C.len x y
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
    if verify C (point C.len xB yB) e sig then throw s!"{m}: verified with another key"

end VG.Test.Ec.Rfc7027
