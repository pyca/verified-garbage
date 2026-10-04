import VerifiedGarbageTest.Ec.Common
import VerifiedGarbage.Spec.Ecdh

/-!
# Public keys and ECDH, against NIST CAVP's ECC CDH primitive test

For a curve and its section of `KAS_ECC_CDH_PrimitiveTest.txt` (vendored byte
for byte): each vector gives the peer's public key `QCAVS`, the private key
`dIUT`, its public key `QIUT` and the shared secret `ZIUT`, so they test
`publicKey`, `encodePoint`, `decodePublicKey` and `exchange`. The invalid
public keys are derived from them and from the curve's parameters.
-/

namespace VG.Test.Ec.Cdh

open Spec.Weierstrass Spec.EcKey Spec.Ecdh

structure Vector where
  qx : Nat
  qy : Nat
  d : Nat
  ux : Nat
  uy : Nat
  z : Nat

/-- The `[name]` section's vectors (`count` of them). -/
def parse (name : String) (count : Nat) (text : String) : Except String (List Vector) := do
  let ls := ((lines text).dropWhile (· != s!"[{name}]")).drop 1
  let ls := ls.takeWhile (!·.startsWith "[")
  let mut vs : Array Vector := #[]
  let mut cur : List (String × Nat) := []
  for line in ls do
    match line.splitOn " = " with
    | [k, v] =>
      if k == "COUNT" then cur := []
      else
        cur := cur ++ [(k, ← hexNat v)]
        if k == "ZIUT" then
          let get (k : String) : Except String Nat := match cur.lookup k with
            | some v => pure v
            | none => throw s!"missing {k}"
          let qx ← get "QCAVSx"
          let qy ← get "QCAVSy"
          let d ← get "dIUT"
          let ux ← get "QIUTx"
          let uy ← get "QIUTy"
          let z ← get "ZIUT"
          vs := vs.push { qx, qy, d, ux, uy, z }
    | _ => pure ()
  unless vs.size == count do throw s!"expected {count} vectors, got {vs.size}"
  return vs.toList

def checkVector (C : Curve) (i : Nat) (v : Vector) : Except String Unit := do
  let pt := point C.len
  let U : Point C := .affine (Fin.ofNat C.p v.ux) (Fin.ofNat C.p v.uy)
  unless publicKey C v.d == some U do throw s!"vector {i}: public key mismatch"
  unless encodePoint U == pt v.ux v.uy do throw s!"vector {i}: encoding mismatch"
  unless decodePublicKey C (pt v.ux v.uy) == some U do throw s!"vector {i}: decoding failed"
  unless exchange C v.d (pt v.qx v.qy) == some (toBytes C.len v.z) do
    throw s!"vector {i}: shared secret mismatch"
  -- Both sides agree, when the peer's key is the other key pair's.
  let Q : Point C := .affine (Fin.ofNat C.p v.qx) (Fin.ofNat C.p v.qy)
  unless mul v.d Q == .affine (Fin.ofNat C.p v.z) (match mul v.d Q with
      | .affine _ y => y | .infinity => 0) do
    throw s!"vector {i}: dQ"
  -- Invalid public keys: off the curve, a coordinate not below p, the
  -- wrong prefix or length, and compressed.
  let bad := [pt v.qx (v.qy + 1), (0 : Byte) :: (pt v.qx v.qy).drop 1,
    (pt v.qx v.qy).take (2 * C.len), pt v.qx v.qy ++ [0],
    (if v.qy % 2 = 0 then 2 else 3) :: toBytes C.len v.qx]
  for (b, j) in bad.zipIdx do
    if (exchange C v.d b).isSome || (decodePublicKey C b).isSome then
      throw s!"vector {i}: accepted invalid public key {j}"
  for d in [0, C.n, C.n + v.d] do
    if (exchange C d (pt v.qx v.qy)).isSome || (publicKey C d).isSome then
      throw s!"vector {i}: accepted private key {d}"

def checkCurve (C : Curve) : Except String Unit := do
  let pt := point C.len
  -- A coordinate not below `p` that is congruent to a valid one.
  let gx := C.gx
  let gy := C.gy
  unless decodePublicKey C (pt gx gy) == some (G C) do throw "G did not decode"
  if 2 ^ (8 * C.len) > gx + C.p then
    if (decodePublicKey C (pt (gx + C.p) gy)).isSome then throw "accepted x ≥ p"
  if 2 ^ (8 * C.len) > gy + C.p then
    if (decodePublicKey C (pt gx (gy + C.p))).isSome then throw "accepted y ≥ p"
  if (decodePublicKey C [0]).isSome then throw "accepted O"
  unless encodePoint (.infinity : Point C) == [0] do throw "O encoding"
  unless publicKey C 1 == some (G C) do throw "1G ≠ G"
  unless publicKey C (C.n - 1) == some (.affine (Fin.ofNat C.p gx) (-(Fin.ofNat C.p gy))) do
    throw "(n-1)G ≠ -G"

/-- The checks of the `[name]` section's `count` vectors, and of the curve. -/
def check (C : Curve) (name : String) (count : Nat) (text : String) : Except String Unit := do
  let vs ← parse name count text
  for (v, i) in vs.zipIdx do checkVector C i v
  checkCurve C

end VG.Test.Ec.Cdh
