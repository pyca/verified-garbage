import VerifiedGarbageTest.Sha256
import VerifiedGarbage.Spec.Sm3.Contract
import VerifiedGarbage.TCB.Axioms

/-!
# Known-answer tests for the SM3 specification

Read, when this file is built, from the byte-for-byte copies under `vectors/`
(see their `vectors/sources/` manifests):

* draft-sca-cfrg-sm3-02's Appendix A, GB/T 32905-2016's two examples: the
  padded message, every word `W_j` and `W'_j` of each block's message
  expansion, the registers after every iteration of the compression
  function, and the hash value, checked against `pad`, `W`, `W'`, `round`,
  `compress` and `hash`;
* its Appendix B, the hash values of the eighteen examples of GB/T 32918
  (SM2), checked against `hash`;
* pyca/cryptography's six SM3 vectors (`oscca.txt`), checked against `hash`.

So a transcription error in the spec fails the build.
-/

namespace VG.Test.Sm3

open Lean Elab Command Spec.Sm3

def isHex (s : String) : Bool :=
  !s.isEmpty && s.all fun c => ('0' ≤ c ∧ c ≤ '9') ∨ ('A' ≤ c ∧ c ≤ 'F') ∨ ('a' ≤ c ∧ c ≤ 'f')

/-- The bytes of the lines of `text` made only of hex numbers of whole bytes,
leaving out prose, headings, table headers and page breaks. -/
def hexRows (text : String) : Except String (List Byte) := do
  let rows := (text.splitOn "\n").filterMap fun line =>
    let ts := (line.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
    if !ts.isEmpty && ts.all (fun t => t.length % 2 == 0 && isHex t)
    then some (String.join ts) else none
  let some bs := Sha256.unhex (String.join rows).toLower | throw "bad hex"
  return bs

/-- Big-endian words. -/
def words (bs : List Byte) : List Word :=
  (List.range (bs.length / 4)).map fun i => parseBlock (fun k => bs.getD (4 * i + k) 0) 0

/-- The text between `start` and the next `stop` after it. -/
def between (text start stop : String) : Except String String := do
  let some after := (text.splitOn start)[1]? | throw s!"missing {start}"
  unless (after.splitOn stop).length > 1 do throw s!"missing {stop} after {start}"
  return (after.splitOn stop).headD ""

/-- The section of the draft from the heading `start` to the heading `stop`
(headings start a line; the table of contents indents them). -/
def part (text start stop : String) : Except String String :=
  between text ("\n" ++ start) ("\n" ++ stop)

/-- Check one block `B`, compressed into `V`, against its expanded message
(`W_0 … W_67`, then `W'_0 … W'_63` after the line naming them) and the
registers before and after every iteration; return `CF(V, B)`. -/
def checkBlock (V : HashValue) (B : Block) (expansion states : String) :
    Except String HashValue := do
  let ws := words (← hexRows (← between expansion "W_0 W_1" "W'_0 W'_1"))
  let ws' := words (← hexRows ((expansion.splitOn "W'_0 W'_1").getD 1 ""))
  unless ws.length == 68 do throw s!"expected 68 words W_j, got {ws.length}"
  unless ws'.length == 64 do throw s!"expected 64 words W'_j, got {ws'.length}"
  for j in List.range 68 do
    unless W B j == ws.getD j 0 do throw s!"W_{j} differs"
  for j in List.range 64 do
    unless W' B j == ws'.getD j 0 do throw s!"W'_{j} differs"
  let regs := words (← hexRows states)
  unless regs.length == 8 * 65 do throw s!"expected 65 rows of registers, got {regs.length / 8}"
  let row (i : Nat) := (regs.drop (8 * i)).take 8
  unless V.toList == row 0 do throw "initial registers differ"
  let mut v := V
  for j in List.range 64 do
    v := round B v j
    unless v.toList == row (j + 1) do throw s!"registers after iteration {j} differ"
  unless rounds V B 64 == v do throw "rounds differs"
  return compress V B

def block (bs : List Byte) (i : Nat) : Block := parseBlock fun k => bs.getD (64 * i + k) 0

def digest (V : HashValue) : List Byte := V.toList.flatMap wordBytes

/-- Appendix A.1: "abc", one block. -/
def checkExample1 (text : String) : Except String Unit := do
  let msg ← match Sha256.unhex (← between (← part text "A.1.1." "A.1.2.") "as \"" "\"") with
    | some m => pure m
    | none => throw "bad A.1.1 message"
  unless msg.length == 3 do throw "expected a 3-byte message"
  let padded ← hexRows (← part text "A.1.2." "A.1.3.")
  unless pad msg == padded do throw "A.1.2 padded message differs"
  let V ← checkBlock iv (block padded 0) (← part text "A.1.3." "A.1.4.") (← part text "A.1.4." "A.1.5.")
  let y ← hexRows (← part text "A.1.5." "A.2.")
  unless digest V == y do throw "A.1.5 hash value differs from CF(IV, B_0)"
  unless Spec.Sm3.hash msg == y do throw "A.1.5 hash value differs"

/-- Appendix A.2: 64 bytes, two blocks. -/
def checkExample2 (text : String) : Except String Unit := do
  let msg ← hexRows (← part text "A.2.1." "A.2.2.")
  unless msg.length == 64 do throw "expected a 64-byte message"
  let padded ← hexRows (← part text "A.2.2.  Padded Message" "A.2.2.1.")
  unless pad msg == padded do throw "A.2.2 padded message differs"
  let V₁ ← checkBlock iv (block padded 0)
    (← part text "A.2.2.1.1." "A.2.2.1.2.") (← part text "A.2.2.1.2." "A.2.2.2.")
  let V₂ ← checkBlock V₁ (block padded 1)
    (← part text "A.2.2.2.1." "A.2.2.2.2.") (← part text "A.2.2.2.2." "A.2.3.")
  let y ← hexRows (← part text "A.2.3." "Appendix B.")
  unless digest V₂ == y do throw "A.2.3 hash value differs from CF(CF(IV, B_0), B_1)"
  unless compressList iv padded 2 == V₂ do throw "compressList differs"
  unless Spec.Sm3.hash msg == y do throw "A.2.3 hash value differs"

/-- Appendix B: the input and output of each example. -/
def checkAppendixB (text : String) : Except String Unit := do
  for k in List.range 18 do
    let stop := if k + 1 == 18 then "Appendix C." else s!"B.{k + 2}."
    let section_ ← part text s!"B.{k + 1}." stop
    let input ← hexRows (← between section_ "Input:" "Output:")
    let output ← hexRows ((section_.splitOn "Output:").getD 1 "")
    unless output.length == 32 do throw s!"B.{k + 1}: expected a 32-byte output"
    unless Spec.Sm3.hash input == output do throw s!"B.{k + 1}: hash value differs"

/-- The memory layouts of the contracts: `stateAt` reads native (little-endian)
`u32`s, the buffer follows the hash value. -/
def checkLayouts : Except String Unit := do
  let msg : List Byte := (List.range 70).map (BitVec.ofNat 8 ·)
  let V := compressList iv msg 1
  let state : List Byte :=
    V.toList.flatMap (fun w => (wordBytes w).reverse) ++ msg.drop 64
  let mem : Mem := fun p => state.getD p.toNat 0
  unless stateAt mem 0 == V do throw "stateAt differs"
  unless bytesAt mem 32 6 == msg.drop 64 do throw "bytesAt differs"
  unless (List.finRange 16).map (blockAt (fun p => msg.getD p.toNat 0) 0) ==
      (List.finRange 16).map (block msg 0) do
    throw "blockAt differs"
  unless compressBlocks iv (fun p => msg.getD p.toNat 0) 0 1 == V do
    throw "compressBlocks differs"

run_cmd do
  -- This file is `lean/VerifiedGarbageTest/Sm3.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let draft ← IO.FS.readFile
    (root / "vectors" / "draft-sca-cfrg-sm3" / "draft-sca-cfrg-sm3-02.txt")
  match checkExample1 draft *> checkExample2 draft *> checkAppendixB draft *> checkLayouts with
  | .ok () => pure ()
  | .error e => throwError "SM3 (draft-sca-cfrg-sm3-02): {e}"
  let text ← IO.FS.readFile (root / "vectors" / "cryptography-sm3" / "oscca.txt")
  let vs ← match Sha256.vectors text with
    | .ok vs => pure vs
    | .error e => throwError "oscca.txt: {e}"
  unless vs.length == 6 do throwError "expected 6 vectors, got {vs.length}"
  for (msg, md) in vs do
    unless Spec.Sm3.hash msg == md do throwError "SM3 of the {msg.length}-byte oscca.txt vector is wrong"

#assert_standard_axioms VG.Spec.Sm3.compressContract
#assert_standard_axioms VG.Spec.Sm3.initContract
#assert_standard_axioms VG.Spec.Sm3.updateContract
#assert_standard_axioms VG.Spec.Sm3.finalizeContract

end VG.Test.Sm3
