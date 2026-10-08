import Lean.Elab.Command
import VerifiedGarbage.Spec.Camellia.Contract
import VerifiedGarbage.TCB.Axioms

/-!
# Camellia specification tests

Reads the unmodified published files under `vectors/` (provenance in
`vectors/sources/`): RFC 3713, whose SBOX1 table (§2.4.1) and `Sigma`
constants (§2.2) are compared with the specification's, and whose three
example vectors (Appendix A) are checked; and NTT's known-answer tests for
128-, 192- and 256-bit keys (1,280 each), as pyca/cryptography vendors them.
Every vector is checked in both directions, on its own and as ECB on all of
its key's blocks at once, and every key's schedule is checked to read back
from the layout `vg_camellia_expand_key` stores it in.
-/

namespace VG.Test.Camellia

open Lean Elab Command Spec.Camellia

def unhex (s : String) : Except String (List Byte) := do
  let cs := s.toLower.toList.filter (!·.isWhitespace)
  unless cs.length % 2 == 0 do throw "odd number of hex digits"
  let digit (c : Char) : Except String Nat :=
    if '0' ≤ c ∧ c ≤ '9' then .ok (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
    else .error s!"not a hex digit: {c}"
  (List.range (cs.length / 2)).mapM fun i => do
    return BitVec.ofNat 8 (16 * (← digit cs[2 * i]!) + (← digit cs[2 * i + 1]!))

def number (s : String) : Except String Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw s!"not a number: {s}"

def block (bs : List Byte) : Except String Block := do
  unless bs.length == 16 do throw s!"not a 16-byte block: {bs.length}"
  return Vector.ofFn fun i => bs.getD i 0

/-- The schedule reads back from the layout it is stored in. -/
def checkLayout (key : List Byte) : Except String Unit := do
  let sk := expandKey key
  let r := rounds key.length
  unless sk.kw.length == 4 && sk.k.length == r && sk.ke.length == r / 3 - 2 do
    throw s!"wrong number of subkeys for a {key.length}-byte key"
  unless (scheduleWords sk).length == scheduleLength r do throw "wrong schedule length"
  unless (scheduleBytes sk).length == 8 * scheduleLength r do throw "wrong schedule size"
  unless subkeysOfWords r (scheduleWords sk) == sk do throw "the schedule does not read back"
  let bytes := scheduleBytes sk
  let words := (List.range (scheduleLength r)).map fun i => ofBytes 64 ((bytes.drop (8 * i)).take 8)
  unless words == scheduleWords sk do throw "the schedule's words are not big-endian"

/-- One vector, on its own. -/
def checkVector (key : List Byte) (pt ct : Block) : Except String Unit := do
  let sk := expandKey key
  unless encryptBlock sk pt == ct do throw s!"encryption, {key.length}-byte key"
  unless decryptBlock sk ct == pt do throw s!"decryption, {key.length}-byte key"

def checkRfc (text : String) : Except String Unit := do
  -- Every entry of SBOX1 against the RFC's table (in decimal).
  let table := ((text.splitOn "   SBOX1:\n").drop 1).headD ""
  let rows := ((table.splitOn "\n").drop 1).take 16
  let mut entries := []
  for row in rows do
    for e in (((row.splitOn ": ").drop 1).headD "").splitOn " " do
      unless e.isEmpty do entries := entries ++ [BitVec.ofNat 8 (← number e)]
  unless entries == sbox1Table.toList do throw "SBOX1 differs from RFC 3713 §2.4.1"
  unless sbox1 0x3d == 86 do throw "SBOX1[0x3d] is not 86"
  -- The constants.
  let sigmas := [sigma1, sigma2, sigma3, sigma4, sigma5, sigma6]
  for i in List.range 6 do
    let some v := ((text.splitOn s!"   Sigma{i + 1} = 0x").drop 1).head?
      | throw s!"no Sigma{i + 1}"
    unless ofBytes 64 (← unhex ((v.splitOn ";").headD "")) == sigmas.getD i 0 do
      throw s!"Sigma{i + 1} differs from RFC 3713 §2.2"
  -- Appendix A: a key may continue on the next line, after a colon.
  let excerpt := ((text.splitOn "Appendix A.  Example Data of Camellia").drop 1).headD ""
  let records := (excerpt.splitOn "-bit key\n").drop 1
  unless records.length == 3 do throw s!"expected 3 RFC vectors, got {records.length}"
  for record in records do
    let lines := (record.splitOn "\n").map (·.trimAscii.toString)
    let value (l : String) := (((l.splitOn ":").drop 1).headD "")
    let some i := lines.findIdx? (·.startsWith "Key") | throw "no key"
    let mut keyHex := value (lines.getD i "")
    for l in lines.drop (i + 1) do
      if !l.startsWith ":" then break
      keyHex := keyHex ++ value l
    let key ← unhex keyHex
    let some pt := lines.find? (·.startsWith "Plaintext") | throw "no plaintext"
    let some ct := lines.find? (·.startsWith "Ciphertext") | throw "no ciphertext"
    checkLayout key
    checkVector key (← block (← unhex (value pt))) (← block (← unhex (value ct)))

/-- NTT's vectors: a key (`K No.001 : …`), then plaintexts and ciphertexts
(`P No.001 : …`, `C No.001 : …`) under it. -/
def checkNtt (bits : Nat) (text : String) : Except String Unit := do
  let mut key : List Byte := []
  let mut pt : List Byte := []
  let mut pts : List Block := []
  let mut cts : List Block := []
  let mut count := 0
  let flush (key : List Byte) (pts cts : List Block) : Except String Unit := do
    unless pts.isEmpty do
      let sk := expandKey key
      unless ecb sk .encrypt pts == cts do throw "ECB encryption"
      unless ecb sk .decrypt cts == pts do throw "ECB decryption"
  for line in text.splitOn "\n" do
    match line.splitOn " : " with
    | [tag, hex] =>
      let bytes ← unhex hex
      if tag.startsWith "K No." then
        flush key pts cts
        unless bytes.length == bits / 8 do throw s!"not a {bits}-bit key"
        key := bytes; pts := []; cts := []
        checkLayout key
      else if tag.startsWith "P No." then pt := bytes
      else if tag.startsWith "C No." then
        let p ← block pt
        let c ← block bytes
        checkVector key p c
        pts := pts ++ [p]; cts := cts ++ [c]
        count := count + 1
      else throw s!"unexpected line: {line}"
    | _ => pure ()
  flush key pts cts
  unless count == 1280 do throw s!"expected 1280 {bits}-bit vectors, got {count}"

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let rfc ← IO.FS.readFile (root / "vectors" / "rfc3713" / "rfc3713.txt")
  let mut ntt := []
  for bits in [128, 192, 256] do
    ntt := ntt ++ [(bits, ← IO.FS.readFile
      (root / "vectors" / s!"cryptography-camellia-{bits}" / s!"camellia-{bits}-ecb.txt"))]
  let result := do
    checkRfc rfc
    for (bits, text) in ntt do
      checkNtt bits text
    unless ecb (expandKey (List.replicate 16 0)) .encrypt [] == [] do throw "empty ECB"
  match result with
  | .ok () => pure ()
  | .error e => throwError "Camellia: {e}"

#assert_standard_axioms VG.Spec.Camellia.expandKeyContract
#assert_standard_axioms VG.Spec.Camellia.ecbEncryptContract
#assert_standard_axioms VG.Spec.Camellia.ecbDecryptContract

end VG.Test.Camellia
