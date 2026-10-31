module

import Lean.Elab.Command
meta import Lean.Elab.Command
import VerifiedGarbage.Spec.RsaPss
meta import VerifiedGarbage.Spec.RsaPss
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit
meta import VerifiedGarbage.TCB.Audit
import VerifiedGarbageTest.Memo
meta import VerifiedGarbageTest.Memo

/-!
# RSASSA-PSS and MGF1 specification tests

Known answers are parsed from the byte-for-byte NIST CAVP FIPS 186-3
RSASSA-PSS vectors (`vectors/nist-cavp-rsa-pss/`: 1024-, 2048- and 3072-bit
moduli, SHA-1, SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and
SHA-512/256, MGF1 with the same hash function); no vector values are
embedded in this test.

* Signature verification (`SigVerPSS_186-3.rsp`, and
  `SigVerPSS_186-3_TruncatedSHAs.rsp`, which gives no salt): `verify`
  accepts exactly the vectors that pass, with the salt length of the
  vector's salt (`SaltVal`; `00` is the empty salt) and with any salt
  length; and, for those that pass, rejects a salt one octet longer or
  shorter.
* Signature generation (`SigGenPSS_186-3.txt`, `..._TruncatedSHAs.txt`, which
  give `d` and the salt): `encodeK` of the message's digest with the salt is
  `S^e mod n` as `k` octets, `verify` accepts `S`, `S` is `EM^d mod n`, and
  `sign` gives `S` with the key in CRT form (its factors recovered from `d`
  by `recoverPrimes`); it refuses a salt too long and a digest of the wrong
  length.
-/

namespace VG.Test.RsaPss

open Lean Elab Command Spec Spec.RsaPss Spec.Mgf1

/-- A hexadecimal string as octets (an even number of digits). -/
def hexBytes (s : String) : Except String (List Byte) := do
  let digit (c : Char) : Except String Nat :=
    if '0' ≤ c && c ≤ '9' then pure (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
    else throw s!"invalid hex digit {c}"
  let rec go : List Char → Except String (List Byte)
    | [] => pure []
    | a :: b :: cs => do
      let x := 16 * (← digit a) + (← digit b)
      pure (BitVec.ofNat 8 x :: (← go cs))
    | [_] => throw "odd number of hex digits"
  go s.toList

/-- The hash function a vector names. -/
def hashOf : String → Except String Hash
  | "SHA1" => pure sha1
  | "SHA224" => pure sha224
  | "SHA256" => pure sha256
  | "SHA384" => pure sha384
  | "SHA512" => pure sha512
  | "SHA512224" => pure sha512_224
  | "SHA512256" => pure sha512_256
  | s => throw s!"unknown hash {s}"

/-- A vector: the modulus, `e`, `d` (or empty), the hash function, the
message, the signature, the salt (if given), and whether it passes. -/
structure Vector where
  n : List Byte := []
  e : List Byte := []
  d : List Byte := []
  alg : String := ""
  msg : List Byte := []
  sig : List Byte := []
  salt : Option (List Byte) := none
  pass : Bool := true

/-- The vectors of a file: `n`, `e` and `d` stay until changed, and a vector
ends at its `Result` (`withResult`) or else at its `S` or `SaltVal`, whichever
the file gives last (`last`). -/
def parse (text : String) (last : String) : Except String (List Vector) := do
  let mut cur : Vector := {}
  let mut vs := []
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.startsWith "[" || line.startsWith "#" then continue
    match line.splitOn " = " with
    | [field, value] =>
      let value := value.trimAscii.toString
      match field with
      | "n" => cur := { cur with n := ← hexBytes value }
      | "e" => cur := { cur with e := ← hexBytes value }
      | "d" => cur := { cur with d := ← hexBytes value }
      | "SHAAlg" => cur := { cur with alg := value, salt := none, pass := true }
      | "Msg" => cur := { cur with msg := ← hexBytes value }
      | "S" => cur := { cur with sig := ← hexBytes value }
      | "SaltVal" =>
        let salt ← if value == "00" then pure [] else hexBytes value
        cur := { cur with salt := some salt }
      | "Result" => cur := { cur with pass := value.startsWith "P" }
      | "p" | "q" | "EM with hash moved" | "EM with trailer wrong" => pure ()
      | _ => throw s!"unknown field {field}"
      if field == last then vs := cur :: vs
    | _ => pure ()
  return vs.reverse

/-! The checks of a vector hash the same strings again (the seeds of MGF1
and `M'`, in each `verify`, `encodeK` and `sign`): they use `H` with those
digests computed once, `withTable H`, which is `H` (`withTable_eq`). -/

/-- `H`, with the digests of `table` looked up. -/
def withTable (H : Hash) (table : List (List Byte × List Byte)) : Hash :=
  { H with hash := Test.memo table H.hash }

theorem withTable_eq (H : Hash) (xs ys : List (List Byte)) :
    withTable H (Test.tableOf H.hash xs ++ Test.tableOf H.hash ys) = H := by
  rw [withTable, Test.memo_tableOf_append]

/-- The strings `mgf1 H h maskLen` hashes. -/
def seeds (H : Hash) (h : List Byte) (maskLen : Nat) : List (List Byte) :=
  (List.range ((maskLen + H.len - 1) / H.len)).map fun counter => h ++ Rsa.i2osp counter 4

/-- `H` with the digests computed once that `verify H H v.n v.e mHash v.sig`
computes, whatever the salt length: from the encoding `EM` the signature
gives, as in `verifyEncoding`, MGF1's seeds and then `M'`. -/
def verifyHash (H : Hash) (v : Vector) (mHash : List Byte) : Hash :=
  let k := v.n.length
  let emBits := bitLength (Rsa.os2ip v.n) - 1
  let emLen := emLength emBits
  let z := 8 * emLen - emBits
  let len := emLen - H.len - 1
  let em? := (Rsa.publicOpChecked v.n v.e v.sig).bind fun x =>
    let em := x.drop (k - emLen)
    if em.length = emLen ∧ H.len + 2 ≤ emLen ∧ em.getLast? = some 0xbc ∧
      clearTop z (em.take len) = em.take len then some em else none
  let xs := match em? with
    | some em => seeds H ((em.drop len).take H.len) len
    | none => []
  let t := Test.tableOf H.hash xs
  let ys := match em? with
    | some em =>
      let db := clearTop z (xorBytes (em.take len) (mgf1 (withTable H t) ((em.drop len).take H.len) len))
      match db.dropWhile (· == 0) with
      | 0x01 :: salt => [zeros 8 ++ mHash ++ salt]
      | _ => []
    | none => []
  withTable H (t ++ Test.tableOf H.hash ys)

/-- Checks one signature verification vector. -/
def checkVer (v : Vector) : Except String Unit := do
  let H ← hashOf v.alg
  let mHash := H.hash v.msg
  -- `H` (`withTable_eq`).
  let H' := verifyHash H v mHash
  unless verify H' H' v.n v.e mHash v.sig none == v.pass do throw "verify with any salt length"
  if let some salt := v.salt then
    let sLen := salt.length
    unless verify H' H' v.n v.e mHash v.sig (some sLen) == v.pass do throw "verify"
    if v.pass then
      unless !verify H' H' v.n v.e mHash v.sig (some (sLen + 1)) do throw "accepted sLen + 1"
      if sLen > 0 then
        unless !verify H' H' v.n v.e mHash v.sig (some (sLen - 1)) do throw "accepted sLen - 1"

/-- The CRT form derived from a vector's private key. -/
abbrev CrtKey := List Byte × List Byte × List Byte × List Byte × List Byte

def privateKey (v : Vector) : Except String CrtKey := do
  -- Signing with the CRT form of the key, its factors recovered from `d`.
  let n := Rsa.os2ip v.n
  let k := v.n.length
  let e := Rsa.os2ip v.e
  let (some (p, q), _) := Rsa.recoverPrimes n e (Rsa.os2ip v.d) | throw "factors not found"
  let some (dP, dQ, qInv) := Rsa.crtValues p q (Rsa.os2ip v.d) | throw "no CRT values"
  let pB := Rsa.i2osp p k
  let qB := Rsa.i2osp q k
  return (pB, qB, Rsa.i2osp dP k, Rsa.i2osp dQ k, Rsa.i2osp qInv k)

/-- Checks one signature generation vector with its recovered private key. -/
def checkGen (v : Vector) (key : CrtKey) : Except String Unit := do
  let H ← hashOf v.alg
  let mHash := H.hash v.msg
  let some salt := v.salt | throw "no salt"
  let n := Rsa.os2ip v.n
  let k := v.n.length
  -- `H` with the digests of `M'` and MGF1's seeds computed once: `H`
  -- (`withTable_eq`).
  let emLen := emLength (bitLength n - 1)
  let m' := zeros 8 ++ mHash ++ salt
  let t := Test.tableOf H.hash [m']
  let H' := withTable H (t ++ Test.tableOf H.hash (seeds H ((withTable H t).hash m') (emLen - H.len - 1)))
  let some em := encodeK H' H' v.n mHash salt | throw "encoding failed"
  unless some em == Rsa.publicOp v.n v.e v.sig do throw "encodeK is not S^e mod n"
  unless Rsa.i2osp (Rsa.powMod (Rsa.os2ip em) (Rsa.os2ip v.d) n) k == v.sig do
    throw "S is not EM^d mod n"
  unless verify H' H' v.n v.e mHash v.sig (some salt.length) do throw "verify"
  unless sign H' H' v.n v.e key.1 key.2.1 key.2.2.1 key.2.2.2.1 key.2.2.2.2 mHash salt ==
      .ok v.sig do
    throw "sign"
  -- A salt too long for the modulus, and a digest of the wrong length.
  let long := List.replicate (k - H.len - 1) 0
  unless sign H' H' v.n v.e key.1 key.2.1 key.2.2.1 key.2.2.2.1 key.2.2.2.2 mHash long ==
      .invalid do
    throw "signed with a salt too long"
  unless sign H' H' v.n v.e key.1 key.2.1 key.2.2.1 key.2.2.2.1 key.2.2.2.2 (0 :: mHash) salt ==
      .invalid do
    throw "signed a digest of the wrong length"

/-- Checks every vector of a file; `count` is the number expected. -/
def checkFile (root : System.FilePath) (name last : String) (count : Nat)
    (generation : Bool) : IO (Except String Unit) := do
  let text ← IO.FS.readFile (root / "vectors" / "nist-cavp-rsa-pss" / name)
  return do
    let vs ← parse text last
    unless vs.length == count do throw s!"{name}: {vs.length} vectors"
    -- Prime recovery and CRT conversion depend only on n, e and d, which
    -- remain unchanged across each key's vectors. Reuse that exact setup;
    -- every vector still runs all of its signature and rejection checks.
    let mut cached : Option ((List Byte × List Byte × List Byte) × CrtKey) := none
    for (v, i) in vs.zipIdx do
      let result ← if generation then do
        let identity := (v.n, v.e, v.d)
        let key ← (match cached with
          | some (previous, key) => if previous == identity then pure key else privateKey v
          | none => privateKey v).mapError fun e =>
            s!"{name}: vector {i} ({v.n.length * 8} bits, {v.alg}): {e}"
        cached := some (identity, key)
        pure (checkGen v key)
      else pure (checkVer v)
      match result with
      | .ok () => pure ()
      | .error e => throw s!"{name}: vector {i} ({v.n.length * 8} bits, {v.alg}): {e}"

/-- MGF1 is the hash of the seed and each counter, truncated. -/
def checkMgf1 : Except String Unit := do
  let seed : List Byte := [1, 2, 3]
  for H in hashes do
    for len in [0, 1, H.len - 1, H.len, H.len + 1, 3 * H.len + 5] do
      let blocks := (List.range 4).flatMap fun c =>
        H.hash (seed ++ [0, 0, 0, BitVec.ofNat 8 c])
      unless mgf1 H seed len == blocks.take len do throw s!"MGF1 with {H.name}, {len} octets"
    unless (H.hash []).length == H.len do throw s!"{H.name}: digest length"

#assert_standard_axioms Spec.RsaPss.encodeK
#assert_standard_axioms Spec.RsaPss.verify
#assert_standard_axioms Spec.RsaPss.sign
#assert_no_compiler_overrides Spec.RsaPss.encodeK Spec.RsaPss.verify Spec.RsaPss.sign Spec.Mgf1.mgf1
#assert_spec_origin

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent) | throwError "no repository root"
  match checkMgf1 with
  | .ok () => pure ()
  | .error e => throwError "MGF1: {e}"
  for (name, last, count, generation) in [
      ("SigVerPSS_186-3.rsp", "Result", 270, false),
      ("SigVerPSS_186-3_TruncatedSHAs.rsp", "Result", 108, false),
      ("SigGenPSS_186-3.txt", "SaltVal", 80, true),
      ("SigGenPSS_186-3_TruncatedSHAs.txt", "SaltVal", 40, true)] do
    match ← checkFile root name last count generation with
    | .ok () => pure ()
    | .error e => throwError "{e}"

end VG.Test.RsaPss
