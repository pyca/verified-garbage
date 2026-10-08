import VerifiedGarbageTest.Aes
import VerifiedGarbage.Spec.Ctr

/-!
# Known-answer tests for the CTR specification

The AES-CTR test vectors of RFC 3686 §6 (three for each of 128-, 192- and
256-bit keys, of 16, 32 and 36 bytes), read from the unmodified RFC under
`vectors/rfc3686/` (see `vectors/sources/`) when this file is built and
checked against `VG.Spec.Ctr.aesCtr` from the first counter block, so that
a transcription error in the spec fails the build. RFC 3686's counter
blocks (a nonce, an IV and a 32-bit block counter from 1) are counter
blocks of SP 800-38A's standard incrementing function while the block
counter does not wrap, as in every vector. Each vector is checked:
* in both directions;
* against each counter block and key stream block it lists (`Tⱼ` and
  `CIPH_K(Tⱼ)`);
* in two pieces, the first block and the rest, with the second piece
  continuing from `Ctr.next` of the first: the chaining the function
  implemented in assembly relies on;
* truncated to each length that ends in its last block.

The increment is also checked to carry across bytes and to wrap from
`1¹²⁸` to `0¹²⁸`, which no vector reaches.
-/

namespace VG.Test.Ctr

open Lean Elab Command Spec.Ctr

/-- The contents of `vectors/<path>`. -/
def readFile (path : System.FilePath) : CommandElabM String := do
  -- This file is `lean/VerifiedGarbageTest/<File>.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  IO.FS.readFile (root / "vectors" / path)

/-- The test vectors of RFC 3686 §6: for each, its fields `label: hex …`,
with the hex of the lines `: hex …` that continue them. Labels are in lower
case with single spaces (the RFC writes both `Counter Block (1)` and
`Counter block (1)`, `Key Stream    (1)` and `Key stream    (1)`). -/
def vectors (text : String) : List (List (String × String)) :=
  -- The section itself, not its line in the table of contents.
  let section_ := ((text.splitOn "6.  Test Vectors").getLastD "").splitOn "7.  Security Considerations"
  ((section_.headD "").splitOn "Test Vector #").drop 1 |>.map fun v => Id.run do
    let mut out : Array (String × String) := #[]
    for l in v.splitOn "\n" do
      match l.splitOn ":" with
      | [label, value] =>
        let label := " ".intercalate ((label.toLower.splitOn " ").filter (· ≠ ""))
        let hex := String.join ((value.splitOn " ").filter (· ≠ "")) |>.trimAscii.toString
        if label.isEmpty then
          if !out.isEmpty then out := out.modify (out.size - 1) fun (k, w) => (k, w ++ hex)
        else out := out.push (label, hex)
      | _ => pure ()
    return out.toList

run_cmd do
  let vs := vectors (← readFile ("rfc3686" / "rfc3686.txt"))
  unless vs.length == 9 do throwError "RFC 3686: {vs.length} test vectors, not 9"
  let mut keyLens : List Nat := []
  for (v, i) in vs.zipIdx 1 do
    let get (k : String) : CommandElabM (List Byte) := do
      let some s := v.lookup k | throwError "RFC 3686, test vector #{i}: no `{k}`"
      let some bs := Test.Sha256.unhex s.toLower
        | throwError "RFC 3686, test vector #{i}: `{k}` is not hex"
      pure bs
    let key ← get "aes key"
    let t ← get "counter block (1)"
    let pt ← get "plaintext"
    let ct ← get "ciphertext"
    unless t.length == 16 && pt.length == ct.length && 16 < pt.length + 1 do
      throwError "RFC 3686, test vector #{i}: unexpected lengths"
    keyLens := keyLens ++ [key.length]
    unless aesCtr key t pt == ct && aesCtr key t ct == pt do
      throwError "RFC 3686, test vector #{i}: AES-CTR is wrong"
    let ciph := Spec.Cbc.aesWith (Spec.Aes.rounds (key.length / 4)) (Spec.Aes.expandKey key)
    let n := (pt.length + 15) / 16
    for (tj, j) in (counters t n).zipIdx 1 do
      unless tj == (← get s!"counter block ({j})") do
        throwError "RFC 3686, test vector #{i}: counter block {j} is wrong"
      unless ciph tj == (← get s!"key stream ({j})") do
        throwError "RFC 3686, test vector #{i}: key stream block {j} is wrong"
    -- In two pieces, the second from the counter block the first leaves.
    let whole := pt.take (16 * (pt.length / 16))
    let bs := Spec.Cbc.blocks whole
    unless (crypt ciph t (bs.take 1) ++ crypt ciph (next t 1) (bs.drop 1)).flatten ==
        ct.take whole.length do
      throwError "RFC 3686, test vector #{i}: AES-CTR in two pieces is wrong"
    -- With a partial last block.
    for len in List.range' (16 * (n - 1) + 1) (pt.length - 16 * (n - 1)) do
      unless aesCtr key t (pt.take len) == ct.take len do
        throwError "RFC 3686, test vector #{i}: AES-CTR of {len} bytes is wrong"
  unless keyLens == [16, 16, 16, 24, 24, 24, 32, 32, 32] do
    throwError "RFC 3686: keys of {keyLens} bytes"

-- The increment carries across bytes, and wraps.
#guard inc (List.replicate 14 0 ++ [0x01, 0xff]) == List.replicate 14 0 ++ [0x02, 0x00]
#guard inc (List.replicate 16 0xff) == List.replicate 16 0
#guard inc (0x7f :: List.replicate 15 0xff) == 0x80 :: List.replicate 15 0
#guard next (List.replicate 16 0xff) 2 == List.replicate 15 0 ++ [0x01]

end VG.Test.Ctr
