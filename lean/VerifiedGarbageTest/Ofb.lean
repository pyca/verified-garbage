import VerifiedGarbageTest.Cbc
import VerifiedGarbage.Spec.Ofb

/-!
# Known-answer tests for the OFB specification

The NIST CAVP AES-OFB multi-block message tests (`OFBMMT`, for 128-, 192-
and 256-bit keys), read from the vendored response files under
`vectors/nist-cavp-aes-mmt/` (see `vectors/sources/`) when this file is
built and checked against `VG.Spec.Ofb.aesOfb`, so that a transcription
error in the spec fails the build. Every vector is checked: ten in each
direction for each key length, of one to ten blocks.

Each vector is also checked:
* in two pieces, the first block and the rest, with the second piece
  continuing from `Ofb.next` of the first: the chaining the function
  implemented in assembly relies on;
* truncated to each length that ends in its last block (the partial last
  block of §6.4 is the matching prefix of the output).
-/

namespace VG.Test.Ofb

open Lean Elab Command Test.Aes Spec.Ofb

run_cmd do
  let mut n : Nat := 0
  for bits in [128, 192, 256] do
    let name := s!"OFBMMT{bits}.rsp"
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
            ct.length == pt.length && 0 < pt.length do
          throwError "{name}, COUNT = {count}: unexpected lengths"
        let ciph := Spec.Cbc.aesWith (Spec.Aes.rounds (key.length / 4)) (Spec.Aes.expandKey key)
        let (input, output) := if dir == "ENCRYPT" then (pt, ct) else (ct, pt)
        unless aesOfb key iv input == output do
          throwError "{name}, COUNT = {count}: AES-OFB {dir} is wrong"
        -- In two pieces, the second from the block the first leaves.
        let bs := Spec.Cbc.blocks input
        let iv' := next ciph iv 1
        unless (crypt ciph iv (bs.take 1) ++ crypt ciph iv' (bs.drop 1)).flatten == output do
          throwError "{name}, COUNT = {count}: AES-OFB {dir} in two pieces is wrong"
        -- With a partial last block.
        for k in List.range 15 do
          let len := input.length - 15 + k
          unless aesOfb key iv (input.take len) == output.take len do
            throwError "{name}, COUNT = {count}: AES-OFB {dir} of {len} bytes is wrong"
        n := n + 1
  unless n == 60 do throwError "expected 60 vectors, checked {n}"

end VG.Test.Ofb
