import Lean.Elab.Command
import VerifiedGarbage.Spec.Seed.Contract
import VerifiedGarbage.TCB.Axioms

/-!
# SEED specification tests

Reads the unmodified published files under `vectors/` (provenance in
`vectors/sources/`). From RFC 4269: every byte of the S-boxes S0 and S1
(Appendix A.1) against the spec's transcription, every entry of the four
extended SS-boxes (Appendix A.2) against the spec's G, and the four
Appendix B vectors in both directions, with their round keys and the input
of every round. From pyca/cryptography: the CBC vectors of RFC 4196 and
the OFB and CFB128 vectors, each block of which is a known answer for one
SEED encryption, and, inverted, for one decryption (230 blocks in all).
-/

namespace VG.Test.Seed

open Lean Elab Command Spec.Seed

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

/-- The comma-separated tokens of the lines that hold only tokens of
`digits` hex digits: a table's rows, without the page headers and footers
between them. -/
def tableTokens (text : String) (digits : Nat) : List String :=
  (text.splitOn "\n").flatMap fun line =>
    let tokens := ((line.splitOn ",").map (·.trimAscii.toString)).filter (!·.isEmpty)
    if !tokens.isEmpty && tokens.all (fun t => t.length == digits && isHex t) then tokens
    else []

def checkSboxes (text : String) : Except String Unit := do
  let s0Text ← between text "- S-Box S0" "- S-Box S1"
  let s1Text ← between text "- S-Box S1" "A.2."
  let s0Bytes ← unhex (String.join (tableTokens s0Text 2))
  let s1Bytes ← unhex (String.join (tableTokens s1Text 2))
  unless s0Bytes == s0.toList do throw "S0 differs from RFC 4269 Appendix A.1"
  unless s1Bytes == s1.toList do throw "S1 differs from RFC 4269 Appendix A.1"
  -- G is the XOR of the SS-boxes of its four bytes (§2.2): with the other
  -- three bytes zero, G of byte `k` is `SSk` and the other boxes' entry 0.
  let ss ← [("- S-Box SS0", "- S-Box SS1"), ("- S-Box SS1", "- S-Box SS2"),
      ("- S-Box SS2", "- S-Box SS3"), ("- S-Box SS3", "Appendix B")].mapM fun (a, b) => do
    let words ← (tableTokens (← between text a b) 8).mapM word
    unless words.length == 256 do throw s!"{a}: {words.length} entries"
    return words
  for k in List.range 4 do
    let others := (List.range 4).foldl (fun acc i =>
      if i == k then acc else acc ^^^ (ss.getD i []).getD 0 0) 0
    for x in List.range 256 do
      unless g (BitVec.ofNat 32 (x <<< (8 * k))) == ((ss.getD k []).getD x 0 ^^^ others) do
        throw s!"G differs from SS{k} of RFC 4269 Appendix A.2 at {x}"

structure RfcVector where
  key : List Byte := []
  pt : List Byte := []
  ct : List Byte := []
  /-- Each round's `Ki0`, `Ki1`, and its input `L0`, `L1`, `R0`, `R1`. -/
  rounds : List (List Word) := []

def checkRfcVectors (text : String) : Except String Unit := do
  let mut vectors : Array RfcVector := #[]
  for line in (← between text "Appendix B." "Full Copyright Statement").splitOn "\n" do
    let line := line.trimAscii.toString
    match line.splitOn " : " with
    | [label, value] =>
      let label := label.trimAscii.toString
      if label == "Key" then
        vectors := vectors.push { key := ← unhex value }
      else if label == "Plaintext" || label == "Ciphertext" || label.startsWith "Round" then
        let some v := vectors.back? | throw s!"{label} before a key"
        let v ← if label == "Plaintext" then pure { v with pt := ← unhex value }
          else if label == "Ciphertext" then pure { v with ct := ← unhex value }
          else do
            let words ← ((value.replace "|" " ").splitOn " " |>.filter (!·.isEmpty)).mapM word
            unless words.length == 6 do throw s!"bad round line: {line}"
            pure { v with rounds := v.rounds ++ [words] }
        vectors := vectors.pop.push v
    | _ => pure ()
  unless vectors.size == 4 do throw s!"expected 4 RFC 4269 vectors, got {vectors.size}"
  for v in vectors do
    let key ← block v.key
    let pt ← block v.pt
    let ct ← block v.ct
    unless v.rounds.length == 16 do throw "expected 16 rounds"
    let k := expandKey key
    let mut state := (wordAt pt 0, wordAt pt 4, wordAt pt 8, wordAt pt 12)
    for j in List.range 16 do
      let r := v.rounds.getD j []
      unless roundKey k j == (r.getD 0 0, r.getD 1 0) do throw s!"round key {j + 1} differs"
      unless state == (r.getD 2 0, r.getD 3 0, r.getD 4 0, r.getD 5 0) do
        throw s!"input of round {j + 1} differs"
      state := round (roundKey k j) state
    unless encryptBlock k pt == ct do throw "RFC 4269 encryption failed"
    unless decryptBlock k ct == pt do throw "RFC 4269 decryption failed"
    unless ecb k .encrypt [pt, ct] == [ct, encryptBlock k ct] do throw "ECB encryption failed"
    unless ecb k .decrypt [ct, pt] == [pt, decryptBlock k pt] do throw "ECB decryption failed"

abbrev Fields := List (String × String)

def fields (text : String) : Fields :=
  (text.splitOn "\n").filterMap fun line =>
    match line.trimAscii.toString.splitOn " = " with
    | [k, v] => some (k, v)
    | _ => none

def get (fs : Fields) (k : String) : Except String (List Byte) :=
  match fs.lookup k with
  | some v => unhex v
  | none => throw s!"missing {k}"

def xor (a b : Block) : Block := Vector.ofFn fun i => a[i] ^^^ b[i]

inductive Mode | cbc | ofb | cfb

/-- Each record's blocks as known answers of single SEED operations: in
CBC, `E(P ^ C') = C`; in OFB, `E(O') = O` for the output `O = P ^ C`; in
CFB, `E(C') ^ P = C`, where `'` is the previous block (the IV at first).
Each is also checked inverted, by decryption. Returns the blocks checked. -/
def checkModes (text : String) (mode : Mode) (records : Nat) : Except String Nat := do
  let mut count := 0
  let mut blocks := 0
  for record in text.replace "\r" "" |>.splitOn "\n\n" do
    let fs := fields record
    let some _ := fs.lookup "COUNT" | continue
    let k := expandKey (← block (← get fs "KEY"))
    let pt ← get fs "PLAINTEXT"
    let ct ← get fs "CIPHERTEXT"
    unless pt.length % 16 == 0 && pt.length == ct.length && pt.length > 0 do
      throw "bad vector lengths"
    let mut prev ← block (← get fs "IV")
    for i in List.range (pt.length / 16) do
      let p ← block ((pt.drop (16 * i)).take 16)
      let c ← block ((ct.drop (16 * i)).take 16)
      let (input, output) := match mode with
        | .cbc => (xor p prev, c)
        | .ofb => (prev, xor p c)
        | .cfb => (prev, xor p c)
      unless ecb k .encrypt [input] == [output] do throw s!"encryption failed at record {count}"
      unless ecb k .decrypt [output] == [input] do throw s!"decryption failed at record {count}"
      prev := match mode with | .cbc | .cfb => c | .ofb => output
      blocks := blocks + 1
    count := count + 1
  unless count == records do throw s!"expected {records} records, got {count}"
  return blocks

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let read (dir name : String) := IO.FS.readFile (root / "vectors" / dir / name)
  let rfc ← read "rfc4269" "rfc4269.txt"
  let cbc ← read "cryptography-seed-cbc" "rfc-4196.txt"
  let ofb ← read "cryptography-seed-ofb" "seed-ofb.txt"
  let cfb ← read "cryptography-seed-cfb" "seed-cfb.txt"
  let result := do
    checkSboxes rfc
    checkRfcVectors rfc
    let a ← checkModes cbc .cbc 2
    let b ← checkModes ofb .ofb 20
    let c ← checkModes cfb .cfb 20
    unless a + b + c == 226 do throw s!"expected 226 mode blocks, got {a + b + c}"
  match result with
  | .ok () => pure ()
  | .error e => throwError "SEED: {e}"

#assert_standard_axioms VG.Spec.Seed.expandKeyContract
#assert_standard_axioms VG.Spec.Seed.ecbEncryptContract
#assert_standard_axioms VG.Spec.Seed.ecbDecryptContract

end VG.Test.Seed
