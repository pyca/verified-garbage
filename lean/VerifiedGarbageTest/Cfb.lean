import VerifiedGarbageTest.Cbc
import VerifiedGarbage.Spec.Cfb

/-!
# Known-answer tests for the CFB128 specification

The NIST CAVP AES-CFB128 multi-block message tests (`CFB128MMT`, for 128-,
192- and 256-bit keys), read from the vendored response files under
`vectors/nist-cavp-aes-mmt/` (see `vectors/sources/`) when this file is
built and checked against `VG.Spec.Cfb.aesCfbEncrypt` (the `ENCRYPT`
vectors) and `VG.Spec.Cfb.aesCfbDecrypt` (the `DECRYPT` vectors), so that a
transcription error in the spec fails the build. Every vector is checked:
ten in each direction for each key length, of one to ten blocks.

Each vector is also checked in two pieces, the first block and the rest,
with the second piece continuing from `Cbc.next` of the first: the
chaining the functions implemented in assembly rely on.
-/

namespace VG.Test.Cfb

open Lean Elab Command Test.Aes Spec.Cfb

run_cmd do
  let mut n : Nat := 0
  for bits in [128, 192, 256] do
    let name := s!"CFB128MMT{bits}.rsp"
    for dir in ["ENCRYPT", "DECRYPT"] do
      let rs := (records (← Test.Cbc.readMmt name)).filter (·.params.any (·.1 == dir))
      unless rs.length == 10 do throwError "{name}: {rs.length} {dir} vectors, not 10"
      for r in rs do
        let v : Except String _ := do
          pure (← r.bytes "KEY", ← r.bytes "IV", ← r.bytes "PLAINTEXT", ← r.bytes "CIPHERTEXT")
        let (key, iv, pt, ct) ← match v with
          | .ok x => pure x
          | .error e => throwError "{name}: {e}"
        let count := (r.get "COUNT").toOption
        unless key.length == bits / 8 && iv.length == 16 && pt.length % 16 == 0 &&
            ct.length == pt.length do
          throwError "{name}, COUNT = {count}: unexpected lengths"
        let ciph := Spec.Cbc.aesWith (Spec.Aes.rounds (key.length / 4)) (Spec.Aes.expandKey key)
        let (input, output) := if dir == "ENCRYPT" then (pt, ct) else (ct, pt)
        let run (iv : List Byte) (bs : List (List Byte)) : List (List Byte) :=
          if dir == "ENCRYPT" then encrypt ciph iv bs else decrypt ciph iv bs
        let whole := if dir == "ENCRYPT" then aesCfbEncrypt key iv pt else aesCfbDecrypt key iv ct
        unless whole == output do
          throwError "{name}, COUNT = {count}: AES-CFB128 {dir} is wrong"
        -- In two pieces, the second from the ciphertext block the first ends with.
        let bs := Spec.Cbc.blocks input
        let first := run iv (bs.take 1)
        let iv' := Spec.Cbc.next iv (if dir == "ENCRYPT" then first else bs.take 1)
        unless (first ++ run iv' (bs.drop 1)).flatten == output do
          throwError "{name}, COUNT = {count}: AES-CFB128 {dir} in two pieces is wrong"
        n := n + 1
  unless n == 60 do throwError "expected 60 vectors, checked {n}"

end VG.Test.Cfb
