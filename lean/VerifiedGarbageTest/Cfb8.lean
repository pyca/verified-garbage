import VerifiedGarbageTest.Cbc
import VerifiedGarbage.Spec.Cfb8

/-!
# Known-answer tests for the CFB8 specification

The NIST CAVP AES-CFB8 multi-block message tests (`CFB8MMT`, for 128-, 192-
and 256-bit keys), read from the vendored response files under
`vectors/nist-cavp-aes-mmt/` (see `vectors/sources/`) when this file is
built and checked against `VG.Spec.Cfb8.aesCfb8Encrypt` (the `ENCRYPT`
vectors) and `VG.Spec.Cfb8.aesCfb8Decrypt` (the `DECRYPT` vectors), so that
a transcription error in the spec fails the build. Every vector is checked:
ten in each direction for each key length, of one to ten bytes.

Each vector is also checked in two pieces, split after each byte, with the
second piece continuing from `next` of the first: the chaining the
functions implemented in assembly rely on.
-/

namespace VG.Test.Cfb8

open Lean Elab Command Test.Aes Spec.Cfb8

run_cmd do
  let mut n : Nat := 0
  for bits in [128, 192, 256] do
    let name := s!"CFB8MMT{bits}.rsp"
    for dir in ["ENCRYPT", "DECRYPT"] do
      let rs := (records (← Test.Cbc.readMmt name)).filter (·.params.any (·.1 == dir))
      unless rs.length == 10 do throwError "{name}: {rs.length} {dir} vectors, not 10"
      for r in rs do
        let v : Except String _ := do
          pure (← r.bytes "KEY", ← r.bytes "IV", ← r.bytes "PLAINTEXT", ← r.bytes "CIPHERTEXT")
        let (key, iv, pt, ct) ← match v with
          | .ok x => pure x
          | .error e => throwError "{name}, {e}"
        let count := (r.get "COUNT").toOption
        unless key.length == bits / 8 && iv.length == 16 && ct.length == pt.length do
          throwError "{name}, COUNT = {count}: unexpected lengths"
        let ciph := Spec.Cbc.aesWith (Spec.Aes.rounds (key.length / 4)) (Spec.Aes.expandKey key)
        let (input, output) := if dir == "ENCRYPT" then (pt, ct) else (ct, pt)
        let run (iv : List Byte) (bs : List Byte) : List Byte :=
          if dir == "ENCRYPT" then encrypt ciph iv bs else decrypt ciph iv bs
        let whole := if dir == "ENCRYPT" then aesCfb8Encrypt key iv pt else aesCfb8Decrypt key iv ct
        unless whole == output do
          throwError "{name}, COUNT = {count}: AES-CFB8 {dir} is wrong"
        -- In two pieces, the second from the input block the first ends with.
        for k in List.range (input.length + 1) do
          let first := run iv (input.take k)
          let iv' := next iv (if dir == "ENCRYPT" then first else input.take k)
          unless first ++ run iv' (input.drop k) == output do
            throwError "{name}, COUNT = {count}: AES-CFB8 {dir} split after {k} is wrong"
        n := n + 1
  unless n == 60 do throwError "expected 60 vectors, checked {n}"

end VG.Test.Cfb8
