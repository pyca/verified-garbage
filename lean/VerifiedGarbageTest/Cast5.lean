import Lean.Elab.Command
import VerifiedGarbage.Spec.Cast5.Contract
import VerifiedGarbage.TCB.Axioms

/-!
# CAST5 specification tests

Reads the unmodified published files under `vectors/` (provenance in
`vectors/sources/`):

* RFC 2144: every entry of the eight S-boxes of Appendix A is compared with
  the spec's tables, and the three vectors of Appendix B.1 (keys of 40, 80
  and 128 bits, so both 12 and 16 rounds and zero padding) are checked.
* Botan's `cast128.vec`: all 48 vectors, keys of 11 to 16 bytes, one of them
  of two blocks.
* pyca/cryptography's `cast5-cbc.txt`: all 20 CBC vectors (128-bit keys, 1
  to 10 blocks), each block checked as `Cᵢ = E(Pᵢ ⊕ Cᵢ₋₁)` and
  `Pᵢ = D(Cᵢ) ⊕ Cᵢ₋₁`, from the IV.

Every vector is checked in both directions, through `ecb`. RFC 2144
Appendix B.2's maintenance test (a million iterations) is not run.
-/

namespace VG.Test.Cast5

open Lean Elab Command Spec.Cast5

def unhex (s : String) : Except String (List Byte) := do
  let cs := s.toLower.toList.filter (!·.isWhitespace)
  unless cs.length % 2 == 0 do throw "odd number of hex digits"
  let digit (c : Char) : Except String Nat :=
    if '0' ≤ c ∧ c ≤ '9' then .ok (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
    else .error s!"not a hex digit: {c}"
  (List.range (cs.length / 2)).mapM fun i => do
    return BitVec.ofNat 8 (16 * (← digit cs[2 * i]!) + (← digit cs[2 * i + 1]!))

abbrev Fields := List (String × String)

/-- The `key = value` lines of a record, keys in lower case. -/
def fields (text : String) : Fields :=
  (text.splitOn "\n").filterMap fun line =>
    match line.trimAscii.toString.splitOn " = " with
    | [k, v] => some (k.trimAscii.toString.toLower, v.trimAscii.toString)
    | _ => none

def get (fs : Fields) (k : String) : Except String String :=
  match fs.lookup k with
  | some v => pure v
  | none => throw s!"missing {k}"

def blocks (bs : List Byte) : Except String (List Block) := do
  unless bs.length % 8 == 0 do throw s!"not whole blocks: {bs.length} bytes"
  return (List.range (bs.length / 8)).map fun j => Vector.ofFn fun i => bs.getD (8 * j + i.val) 0

def flat (bs : List Block) : List Byte := bs.flatMap Vector.toList

def xorBlock (a b : Block) : Block := Vector.ofFn fun i => a[i] ^^^ b[i]

/-- ECB of `pt` to `ct` under `key`, in both directions. -/
def checkEcb (name : String) (key : List Byte) (pt ct : List Byte) : Except String Unit := do
  unless validKey key.length do throw s!"{name}: invalid key length {key.length}"
  let k := expandKey key
  let n := rounds key.length
  let p ← blocks pt
  let c ← blocks ct
  unless p.length == c.length do throw s!"{name}: plaintext and ciphertext lengths differ"
  unless ecb k n .encrypt p == c do throw s!"{name}: encryption is wrong"
  unless ecb k n .decrypt c == p do throw s!"{name}: decryption is wrong"

def hexWords (s : String) : List String :=
  (s.split (fun c => c.isWhitespace)).toList.map (·.toString) |>.filter fun t =>
    t.length == 8 && t.all fun c => ('0' ≤ c ∧ c ≤ '9') ∨ ('a' ≤ c ∧ c ≤ 'f')

/-- Appendix A against the spec's S-boxes, and Appendix B.1. -/
def checkRfc (text : String) : Except String Unit := do
  let appendixA := (((text.splitOn "Appendix A. S-Boxes\n").drop 1).headD "").splitOn
    "Appendix B. Test Vectors" |>.headD ""
  let boxes := (appendixA.splitOn "S-Box S").drop 1
  unless boxes.length == 8 do throw s!"expected 8 S-boxes, got {boxes.length}"
  let tables := [s1, s2, s3, s4, s5, s6, s7, s8]
  for (box, i) in boxes.zipIdx do
    unless box.startsWith s!"{i + 1}\n" do throw s!"S-box {i + 1} out of order"
    let words ← (hexWords (box.drop 2).toString).mapM fun w => do
      let bs ← unhex w
      return bs.foldl (fun (acc : BitVec 32) b => (acc <<< 8) ||| b.zeroExtend 32) 0
    unless words.length == 256 do throw s!"S-box {i + 1}: {words.length} entries"
    unless words == (tables.getD i s1).toList do throw s!"S-box S{i + 1} differs from RFC 2144"
  let b1 := (((text.splitOn "B.1. Single Plaintext-Key-Ciphertext Sets").drop 1).headD "").splitOn
    "B.2. Full Maintenance Test" |>.headD ""
  let records := (b1.splitOn "-bit").drop 1
  unless records.length == 3 do throw s!"expected 3 vectors in B.1, got {records.length}"
  for (record, bits) in records.zip [128, 80, 40] do
    let fs := fields record
    -- The first `=` line is the key as given; the 80- and 40-bit keys are
    -- followed by their padding to 128 bits, an unnamed `=` line.
    let key ← unhex ((((record.splitOn "=").drop 1).headD "").splitOn "\n" |>.headD "")
    unless 8 * key.length == bits do throw s!"B.1: a {bits}-bit key of {key.length} bytes"
    if bits < 128 then
      let padded ← unhex ((((record.splitOn "=").drop 2).headD "").splitOn "\n" |>.headD "")
      unless padded == key ++ List.replicate (16 - key.length) 0 do throw s!"B.1: {bits}-bit padding"
      unless expandKey padded == expandKey key do throw s!"B.1: {bits}-bit padded schedule differs"
    checkEcb s!"RFC 2144 B.1, {bits}-bit key" key (← unhex (← get fs "plaintext"))
      (← unhex (← get fs "ciphertext"))

/-- Botan's `[CAST-128]` records: `Key`, `In`, `Out`. -/
def checkBotan (text : String) : Except String Nat := do
  let mut count := 0
  for record in text.splitOn "\n\n" do
    let fs := fields record
    let some key := fs.lookup "key" | continue
    checkEcb s!"Botan vector {count}" (← unhex key) (← unhex (← get fs "in")) (← unhex (← get fs "out"))
    count := count + 1
  return count

/-- pyca/cryptography's CBC records, block by block through ECB. -/
def checkCbc (text : String) : Except String Nat := do
  let mut count := 0
  for record in text.splitOn "\n\n" do
    let fs := fields record
    let some key := fs.lookup "key" | continue
    let key ← unhex key
    unless validKey key.length do throw s!"CBC vector {count}: invalid key length"
    let k := expandKey key
    let n := rounds key.length
    let iv ← blocks (← unhex (← get fs "iv"))
    let p ← blocks (← unhex (← get fs "plaintext"))
    let c ← blocks (← unhex (← get fs "ciphertext"))
    unless iv.length == 1 && p.length == c.length do throw s!"CBC vector {count}: lengths"
    let prev := iv ++ c.dropLast
    unless ecb k n .encrypt (List.zipWith xorBlock p prev) == c do
      throw s!"CBC vector {count}: encryption is wrong"
    unless List.zipWith xorBlock (ecb k n .decrypt c) prev == p do
      throw s!"CBC vector {count}: decryption is wrong"
    count := count + 1
  return count

def checkLimits : Except String Unit := do
  for len in List.range 20 do
    unless (decide (validKey len)) == (5 ≤ len && len ≤ 16) do throw s!"validKey {len}"
    if 5 ≤ len && len ≤ 16 then
      unless rounds len == (if len ≤ 10 then 12 else 16) do throw s!"rounds {len}"

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let read (dir name : String) := IO.FS.readFile (root / "vectors" / dir / name)
  match checkRfc (← read "rfc2144" "rfc2144.txt") with
  | .ok () => pure ()
  | .error e => throwError "CAST5: {e}"
  match checkBotan (← read "botan-cast128" "cast128.vec") with
  | .ok 48 => pure ()
  | .ok n => throwError "CAST5: expected 48 Botan vectors, got {n}"
  | .error e => throwError "CAST5: {e}"
  match checkCbc (← read "cryptography-cast5" "cast5-cbc.txt") with
  | .ok 20 => pure ()
  | .ok n => throwError "CAST5: expected 20 CBC vectors, got {n}"
  | .error e => throwError "CAST5: {e}"
  match checkLimits with
  | .ok () => pure ()
  | .error e => throwError "CAST5: {e}"

#assert_standard_axioms VG.Spec.Cast5.expandKeyContract
#assert_standard_axioms VG.Spec.Cast5.ecbEncryptContract
#assert_standard_axioms VG.Spec.Cast5.ecbDecryptContract

end VG.Test.Cast5
