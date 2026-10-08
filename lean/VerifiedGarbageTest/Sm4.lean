import Lean.Elab.Command
import VerifiedGarbage.Spec.Sm4.Contract
import VerifiedGarbage.TCB.Axioms

/-!
# SM4 specification tests

Read the byte-for-byte IETF archive file under `vectors/` (see its
`vectors/sources/` manifest). Check every S-box entry and CK constant,
Appendix A.1's two single-block examples in both directions, all 128
published intermediate round outputs and keys, and both two-block ECB
examples of Appendix A.2.1. The million-iteration examples A.1.3/A.1.6
are not run in the specification build.
-/

namespace VG.Test.Sm4

open Lean Elab Command Spec.Sm4

def unhex (s : String) : Except String (List Byte) := do
  let cs := s.toLower.toList.filter (!·.isWhitespace)
  unless cs.length % 2 == 0 do throw "odd number of hex digits"
  let digit (c : Char) : Except String Nat :=
    if '0' ≤ c ∧ c ≤ '9' then .ok (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
    else .error s!"not a hex digit: {c}"
  (List.range (cs.length / 2)).mapM fun i => do
    return BitVec.ofNat 8 (16 * (← digit cs[2 * i]!) + (← digit cs[2 * i + 1]!))

def isHex (s : String) : Bool :=
  !s.isEmpty && s.all fun c => ('0' ≤ c ∧ c ≤ '9') ∨ ('A' ≤ c ∧ c ≤ 'F') ∨ ('a' ≤ c ∧ c ≤ 'f')

/-- A big-endian word from eight hex digits. -/
def word (s : String) : Except String Word := do
  let bs ← unhex s
  unless bs.length == 4 do throw s!"not a 32-bit word: {s}"
  return bs.foldl (fun w b => (w <<< 8) ||| b.zeroExtend 32) 0

def block (bs : List Byte) : Except String Block := do
  unless bs.length == 16 do throw s!"not a 16-byte block: {bs.length}"
  return Vector.ofFn fun i => bs.getD i 0

/-- The text between `start` and the next `stop` after it. -/
def between (text start stop : String) : Except String String := do
  let some after := (text.splitOn start)[1]? | throw s!"missing {start}"
  return (after.splitOn stop).headD ""


/-- Only complete byte rows, excluding page headers and explanatory prose. -/
def byteRows (text : String) : Except String (List Byte) := do
  let rows := (text.splitOn "\n").filterMap fun line =>
    let ts := (line.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
    if !ts.isEmpty && ts.all (fun t => t.length == 2 && isHex t)
    then some (String.join ts) else none
  unhex (String.join rows)

def checkTables (text : String) : Except String Unit := do
  let mut bytes : List Byte := []
  for line in text.splitOn "\n" do
    match line.splitOn " | " with
    | [label, row] =>
      if label.trimAscii.toString.length == 1 && isHex label.trimAscii.toString then
        bytes := bytes ++ (← unhex row)
    | _ => pure ()
  unless bytes == sbox.toList do throw "S-box differs from Figure 1"
  let mut count := 0
  for line in text.splitOn "\n" do
    let tokens := (line.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
    match tokens with
    | [a, "=", x, b, "=", y] =>
      if a.startsWith "CK_" && b.startsWith "CK_" then
        for (label, value) in [(a, x), (b, y)] do
          let some i := (label.drop 3).toString.toNat? | throw "bad CK index"
          unless ck i == (← word value) do throw s!"CK_{i} differs"
          count := count + 1
    | _ => pure ()
  unless count == 32 do throw s!"expected 32 CK constants, got {count}"
  let mut family : List Word := []
  for line in text.splitOn "\n" do
    let tokens := (line.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
    match tokens with
    | [label, "=", value] =>
      if label.startsWith "FK_" then family := family ++ [← word value]
    | _ => pure ()
  unless family == fk.toList do throw "FK differs"

def part (text start stop : String) : Except String String :=
  between text ("\n" ++ start) ("\n" ++ stop)

def checkExample (text : String) (enc : Bool) : Except String Unit := do
  let key ← block (← byteRows (← between text "Encryption key:" "Status of the round key"))
  let pt ← block (← byteRows (← between text "Plaintext:" (if enc then "Encryption key:" else "!end!")))
  let ct ← block (← byteRows (← between text "Ciphertext:" (if enc then "!end!" else "Encryption key:")))
  let k := expandKey key
  unless encryptBlock k pt == ct do throw "single-block encryption differs"
  unless decryptBlock k ct == pt do throw "single-block decryption differs"
  let mut state := initial (if enc then pt else ct)
  let mut count := 0
  for line in text.splitOn "\n" do
    let tokens := (line.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
    match tokens with
    | [a, "=", rk, b, "=", output] =>
      if a.startsWith "rk_" && b.startsWith "X_" then
        let j := if enc then count else 31 - count
        unless k.getD j 0 == (← word rk) do throw s!"round key {j} differs"
        state := round (k.getD j 0) state
        unless state.2.2.2 == (← word output) do throw s!"round output {count} differs"
        count := count + 1
    | _ => pure ()
  unless count == 32 do throw s!"expected 32 rounds, got {count}"

def blocks (bs : List Byte) : Except String (List Block) := do
  unless bs.length == 32 do throw s!"expected two blocks, got {bs.length} bytes"
  [bs.take 16, bs.drop 16].mapM block

def checkEcb (text : String) : Except String Unit := do
  let pt ← blocks (← byteRows (← between text "Plaintext:" "Encryption Key:"))
  let key ← block (← byteRows (← between text "Encryption Key:" "Ciphertext:"))
  let ct ← blocks (← byteRows (← between text "Ciphertext:" "!end!"))
  let k := expandKey key
  unless ecb k .encrypt pt == ct do throw "two-block ECB encryption differs"
  unless ecb k .decrypt ct == pt do throw "two-block ECB decryption differs"
  unless ecb k .encrypt [] == [] && ecb k .decrypt [] == [] do throw "empty ECB differs"
  -- Splitting a call at a block boundary preserves the result.
  unless ecb k .encrypt (pt ++ pt) == ct ++ ct do throw "ECB concatenation differs"
  -- Contract memory layouts: key bytes are big-endian, schedules little-endian.
  let m : Mem := fun p => key.toList.getD p.toNat 0
  unless blockAt m 0 == key do throw "blockAt differs"
  let scheduleMem : Mem := fun p =>
    ((k.getD (p.toNat / 4) 0) >>> (8 * (p.toNat % 4))).setWidth 8
  unless scheduleAt scheduleMem 0 == k do throw "scheduleAt differs"
  let dataMem : Mem := fun p => (pt.flatMap Vector.toList).getD p.toNat 0
  unless blocksAt dataMem 0 2 == pt do throw "blocksAt differs"

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile
    (root / "vectors" / "draft-ribose-cfrg-sm4" / "draft-ribose-cfrg-sm4-10.txt")
  let result := do
    checkTables text
    checkExample (← part text "A.1.1.  Example 1 (" "A.1.2.  Example 2 (") true
    checkExample (← part text "A.1.2.  Example 2 (" "A.1.3.  Example 3 (") false
    checkExample (← part text "A.1.4.  Example 4" "A.1.5.  Example 5") true
    checkExample (← part text "A.1.5.  Example 5" "A.1.6.  Example 6") false
    checkEcb (← part text "A.2.1.1.  Example 1" "A.2.1.2.  Example 2")
    checkEcb (← part text "A.2.1.2.  Example 2" "A.2.2.  SM4-CBC Examples")
  match result with
  | .ok () => pure ()
  | .error e => throwError "SM4: {e}"

#assert_standard_axioms VG.Spec.Sm4.expandKeyContract
#assert_standard_axioms VG.Spec.Sm4.ecbEncryptContract
#assert_standard_axioms VG.Spec.Sm4.ecbDecryptContract

end VG.Test.Sm4
