module

import VerifiedGarbageTest.Sha256
meta import VerifiedGarbageTest.Sha256
import VerifiedGarbage.Spec.Hkdf
meta import VerifiedGarbage.Spec.Hkdf
import VerifiedGarbage.Spec.Hkdf.Table
meta import VerifiedGarbage.Spec.Hkdf.Table

/-!
# Known-answer tests for the HKDF specification

The test cases of Appendix A of RFC 5869 (three with SHA-256, four with
SHA-1), read from the vendored `vectors/rfc5869/rfc5869.txt` (see
`vectors/sources/`) when this file is built and checked against
`VG.Spec.Hkdf.extract` (the `PRK`) and `VG.Spec.Hkdf.expand` (the `OKM`),
with the HMAC and the digest length that the tables of `Spec/Hkdf/Table.lean`
give each hash function (`HmacTable.hmacOf`), so that a transcription error
fails the build. The cases cover empty and long salts and context
information, and outputs of two and three blocks, the last one partial.
Test case 7 has no salt, which RFC 5869 takes to be `HashLen` zero octets:
both those octets and the empty salt are checked to give its `PRK`, as
`extract`'s documentation says. Expanding to more than 255 blocks is checked
to fail.
-/

namespace VG.Test.Hkdf

open Lean Elab Command
open Spec.Mgf1 (Hash)

/-- A test case: the hash function's name, `IKM`, the salt (`none` if not
provided), `info`, `L`, `PRK` and `OKM`. -/
structure Case where
  hash : String
  ikm : List Byte
  salt : Option (List Byte)
  info : List Byte
  len : Nat
  prk : List Byte
  okm : List Byte

/-- The octets of a field's value: hexadecimal after `0x`, over several
lines, up to `(n octets)`; or none for `(0 octets)`. -/
def octets (v : String) : Except String (List Byte) := do
  let v := (v.splitOn "(").headD ""
  let v := String.join ((v.splitOn " ").filter (· ≠ ""))
  if v.isEmpty then return []
  let some hex := v.dropPrefix? "0x" | throw s!"not hexadecimal: {v}"
  let some bs := Sha256.unhex hex.toString | throw s!"bad hexadecimal: {v}"
  return bs

/-- The fields of a test case's lines: each `Name = value`, with the lines
after it that hold only more of its value (no `=`, and not a page's header
or footer, which start in the first column). -/
def fields (lines : List String) : List (String × String) :=
  lines.foldl (init := []) fun acc l =>
    let t := l.trimAscii.toString
    match t.splitOn " = " with
    | [k, v] => acc ++ [(k.trimAscii.toString, v)]
    | _ =>
      if l.startsWith "   " && !t.isEmpty then
        match acc.getLast? with
        | some (k, v) => acc.dropLast ++ [(k, v ++ " " ++ t)]
        | none => acc
      else acc

/-- The test cases of Appendix A: the lines from each `A.n.  Test Case n`
heading to the next. -/
def cases (text : String) : Except String (List Case) := do
  let lines := text.splitOn "\n"
  let some start := lines.findIdx? (·.startsWith "Appendix A.") | throw "no Appendix A"
  let rest := lines.drop start
  let heads := (List.range rest.length).filter fun i =>
    (rest[i]!).startsWith "A." && ((rest[i]!).splitOn "Test Case").length == 2
  heads.mapM fun i => do
    let body := (rest.drop (i + 1)).takeWhile (!·.startsWith "A.")
    let fs := fields body
    let get (k : String) : Except String String :=
      match fs.lookup k with
      | some v => pure v
      | none => throw s!"no {k} in {rest[i]!}"
    let salt ← get "salt"
    let saltBytes ← if (salt.splitOn "not provided").length == 2 then pure none
      else some <$> octets salt
    let some len := (← get "L").trimAscii.toString.toNat? | throw s!"bad L in {rest[i]!}"
    return {
      hash := (← get "Hash").trimAscii.toString
      ikm := ← octets (← get "IKM")
      salt := saltBytes
      info := ← octets (← get "info")
      len
      prk := ← octets (← get "PRK")
      okm := ← octets (← get "OKM") }

/-- The hash function a case names, as the HMAC tables name it. -/
def hashOf : String → Option Hash
  | "SHA-256" => some Spec.Mgf1.sha256
  | "SHA-1" => some Spec.Mgf1.sha1
  | _ => none

run_cmd do
  -- This file is `lean/VerifiedGarbageTest/Hkdf.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "rfc5869" / "rfc5869.txt")
  let cs ← match cases text with
    | .ok cs => pure cs
    | .error e => throwError "rfc5869.txt: {e}"
  unless cs.map (·.hash) == ["SHA-256", "SHA-256", "SHA-256", "SHA-1", "SHA-1", "SHA-1", "SHA-1"] do
    throwError "expected three SHA-256 cases and four SHA-1 ones, got {cs.map (·.hash)}"
  for c in cs do
    let some H := hashOf c.hash | throwError "unknown hash function {c.hash}"
    let some F := Spec.HmacTable.hmacOf H | throwError "no HMAC over {c.hash}"
    unless c.prk.length == H.len && c.okm.length == c.len do
      throwError "{c.hash} case with L = {c.len}: wrong lengths"
    let salts := match c.salt with
      | some s => [s]
      | none => [List.replicate H.len 0, []]
    for s in salts do
      unless Spec.Hkdf.extract F s c.ikm == c.prk do
        throwError "HKDF-Extract of the {c.hash} case with L = {c.len} is wrong"
    unless Spec.Hkdf.expand F H.len c.prk c.info c.len == some c.okm do
      throwError "HKDF-Expand of the {c.hash} case with L = {c.len} is wrong"
    unless Spec.Hkdf.expand F H.len c.prk c.info (255 * H.len + 1) == none do
      throwError "HKDF-Expand of the {c.hash} case accepts more than 255 blocks"

end VG.Test.Hkdf
