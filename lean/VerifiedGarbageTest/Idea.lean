import Lean.Elab.Command
import VerifiedGarbage.Spec.Idea.Contract

/-!
# Known-answer tests for the IDEA specification

The 900 NESSIE IDEA test vectors (`Idea-128-64.verified.test-vectors`), as
pyca/cryptography reformatted them, read from the unmodified file under
`vectors/cryptography-idea/` (see `vectors/sources/`) when this file is
built, so that a transcription error in the spec fails the build. Every
vector is checked:
* in both directions, by `encryptBlock` and `decryptBlock`, and by `ecb`
  under the encryption and decryption subkeys;
* with ECB on every vector of the same key at once, whole and in two
  pieces, and on no blocks;
* where it gives them, against the ciphertexts of 100 and 1000 iterated
  encryptions (NESSIE's "Iterated 100 times" and "Iterated 1000 times"),
  and that as many decryptions return to the plaintext.

The ⊙-inverse is checked to be an inverse (`mul x (inv x) = 1`) of every
word, `powMod` to be the power, and ⊙ on the edge cases.
-/

namespace VG.Test.Idea

open Lean Elab Command Spec.Idea

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

def fields (text : String) : Fields :=
  (text.splitOn "\n").filterMap fun line =>
    match line.trimAscii.toString.splitOn " = " with
    | [k, v] => some (k, v)
    | _ => none

def bytes (fs : Fields) (k : String) (n : Nat) : Except String (List Byte) := do
  let some v := fs.lookup k | throw s!"missing {k}"
  let bs ← unhex v
  unless bs.length == n do throw s!"{k}: {bs.length} bytes, not {n}"
  return bs

def block (bs : List Byte) : Block := Vector.ofFn fun i => bs.getD i 0

def iterate (f : Block → Block) : Nat → Block → Block
  | 0, b => b
  | n + 1, b => iterate f n (f b)

/-- One vector: `(key, plaintext, ciphertext, [(iterations, ciphertext)])`. -/
abbrev Vector' := Vector Byte 16 × Block × Block × List (Nat × Block)

def parse (text : String) : Except String (List Vector') := do
  let records := (text.splitOn "\n\n").filter (·.contains '=')
  records.mapM fun record => do
    let fs := fields record
    let key ← bytes fs "KEY" 16
    let pt ← bytes fs "PLAINTEXT" 8
    let ct ← bytes fs "CIPHERTEXT" 8
    let mut iterated := []
    for n in [100, 1000] do
      if (fs.lookup s!"CIPHERTEXT{n}").isSome then
        iterated := iterated ++ [(n, block (← bytes fs s!"CIPHERTEXT{n}" 8))]
    return (Vector.ofFn fun i => key.getD i 0, block pt, block ct, iterated)

def check (vs : List Vector') : Except String Unit := do
  unless vs.length == 900 do throw s!"{vs.length} vectors, not 900"
  unless (vs.filter (·.2.2.2.length == 2)).length == 450 do
    throw "expected 450 vectors with iterated ciphertexts"
  let mut keys : List (Vector Byte 16) := []
  for (key, pt, ct, iterated) in vs do
    let e := expandKey key
    let d := invertKey e
    unless encryptBlock key pt == ct && decryptBlock key ct == pt do
      throw s!"vector {key.toList}: IDEA is wrong"
    unless ecb e [pt] == [ct] && ecb d [ct] == [pt] do
      throw s!"vector {key.toList}: ECB is wrong"
    for (n, out) in iterated do
      unless iterate (cryptBlock e) n pt == out && iterate (cryptBlock d) n out == pt do
        throw s!"vector {key.toList}: {n} iterations are wrong"
    unless keys.contains key do keys := keys ++ [key]
  -- ECB of every vector of a key at once, and in two pieces.
  for key in keys do
    let same := vs.filter (·.1 == key)
    let pts := same.map (·.2.1)
    let cts := same.map (·.2.2.1)
    let e := expandKey key
    let d := invertKey e
    unless ecb e pts == cts && ecb d cts == pts do throw s!"key {key.toList}: ECB is wrong"
    for split in List.range (pts.length + 1) do
      unless ecb e (pts.take split) ++ ecb e (pts.drop split) == cts do
        throw s!"key {key.toList}: ECB in two pieces is wrong"
    unless ecb e [] == [] && ecb d [] == [] do throw "ECB of no blocks is not empty"

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "cryptography-idea" / "idea-ecb.txt")
  match parse text >>= check with
  | .ok () => pure ()
  | .error e => throwError "IDEA: {e}"

-- ⊙ on the edge cases: 0 stands for 2¹⁶ ≡ -1.
#guard mul 0 0 == 1
#guard mul 0 1 == 0
#guard mul 1 0 == 0
#guard mul 0 2 == 0xffff
#guard mul 0xffff 0xffff == 4
#guard mul 0x8000 2 == 0
-- The inverse, including of 0 (itself) and 1.
#guard inv 0 == 0
#guard inv 1 == 1
#guard inv 0xffff == 0x8000
#guard (List.range (2 ^ 16)).all fun x =>
  mul (BitVec.ofNat 16 x) (inv (BitVec.ofNat 16 x)) == 1
-- `powMod` is the power.
#guard (List.range 70).all fun a => (List.range 70).all fun e =>
  powMod a e (2 ^ 16 + 1) == a ^ e % (2 ^ 16 + 1)
#guard powMod 3 (2 ^ 16 - 1) (2 ^ 16 + 1) == 3 ^ (2 ^ 16 - 1) % (2 ^ 16 + 1)

end VG.Test.Idea
