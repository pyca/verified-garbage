import VerifiedGarbageTest.Aes
import VerifiedGarbage.Spec.Xts

/-!
# Known-answer tests for the XTS specification

The NIST CAVP XTS-AES tests (`XTSGenAES128` and `XTSGenAES256`, with the
tweak value given as 128 bits), read from the vendored response files under
`vectors/nist-cavp-aes-xts/` (see `vectors/sources/`) when this file is
built and checked against `VG.Spec.Xts.aesXtsEncrypt` and `aesXtsDecrypt`,
so that a transcription error in the spec fails the build. The files have
data units of 128, 256, 200 and 130 bits (128-bit keys) and 256, 384, 140
and 250 bits (256-bit keys); the first 10 vectors of each length that is a
whole number of bytes are checked, in each direction (evaluating the spec
is slow; the Rust tests run all of them against the implementation): whole
blocks, and ciphertext stealing (200 bits, a whole block and 9 bytes). The
data units that are not a whole number of bytes, which no function on bytes
takes, are counted.

Each vector is also checked in the other direction, and those of two or
more blocks in two pieces, the second from `Xts.next` of the first block:
the chaining the functions implemented in assembly rely on.

`mulAlpha` is also checked on the carries of §5.2: within the tweak and out
of its last byte, which wraps into the first as `135`.
-/

namespace VG.Test.Xts

open Lean Elab Command Test.Aes Spec.Xts

/-- The contents of `vectors/<path>`. -/
def readFile (path : System.FilePath) : CommandElabM String := do
  -- This file is `lean/VerifiedGarbageTest/<File>.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  IO.FS.readFile (root / "vectors" / path)

run_cmd do
  let mut checked : Nat := 0
  -- Each file's data unit lengths (bits) and how many vectors of each it has in a direction.
  for (bits, keyLen, lens) in [(128, 32, [(128, 100), (256, 200), (200, 100), (130, 100)]),
      (256, 64, [(256, 100), (384, 200), (140, 100), (250, 100)])] do
    let name := s!"XTSGenAES{bits}.rsp"
    let rs := records (← readFile ("nist-cavp-aes-xts" / name))
    for dir in ["ENCRYPT", "DECRYPT"] do
      let rs := rs.filter (·.params.any (·.1 == dir))
      unless rs.length == 500 do throwError "{name}: {rs.length} {dir} vectors, not 500"
      for (len, n) in lens do
        let rs := rs.filter fun r => (r.get "DataUnitLen").toOption == some (toString len)
        unless rs.length == n do
          throwError "{name}: {rs.length} {dir} vectors of {len} bits"
        if len % 8 != 0 then continue
        for r in rs.take 10 do
          let v : Except String _ := do
            pure (← r.bytes "Key", ← r.bytes "i", ← r.bytes "PT", ← r.bytes "CT")
          let (key, i, pt, ct) ← match v with
            | .ok x => pure x
            | .error e => throwError "{name}: {e}"
          let count := (r.get "COUNT").toOption
          unless key.length == keyLen && i.length == 16 && pt.length == len / 8 && ct.length == pt.length do
            throwError "{name}, {dir}, COUNT = {count}: unexpected lengths"
          unless aesXtsEncrypt key i pt == some ct do
            throwError "{name}, {dir}, COUNT = {count}: XTS-AES encryption is wrong"
          unless aesXtsDecrypt key i ct == some pt do
            throwError "{name}, {dir}, COUNT = {count}: XTS-AES decryption is wrong"
          if 256 ≤ len then
            -- In two pieces, the second from the tweak the first leaves.
            let (enc, dec, t) := keys key i
            let ps := Spec.Cbc.blocks pt
            let cs := Spec.Cbc.blocks ct
            unless crypt enc t (ps.take 1) ++ crypt enc (next t 1) (ps.drop 1) == cs &&
                crypt dec t (cs.take 1) ++ crypt dec (next t 1) (cs.drop 1) == ps do
              throwError "{name}, {dir}, COUNT = {count}: XTS-AES in two pieces is wrong"
          checked := checked + 1
  unless checked == 100 do throwError "expected 100 vectors, checked {checked}"

-- Shorter than a block: no XTS-AES.
#guard aesXtsEncrypt (List.replicate 32 0) (List.replicate 16 0) (List.replicate 15 0) == none
#guard aesXtsDecrypt (List.replicate 32 0) (List.replicate 16 0) (List.replicate 15 0) == none

-- §5.2: a carry from byte 0 into byte 1, and out of byte 15 into byte 0.
#guard mulAlpha (0x80 :: List.replicate 15 0) == [0, 1] ++ List.replicate 14 0
#guard mulAlpha (List.replicate 15 0 ++ [0x80]) == 0x87 :: List.replicate 15 0
#guard mulAlpha (List.replicate 16 0xff) == 0x79 :: List.replicate 15 0xff
#guard next (1 :: List.replicate 15 0) 9 == [0, 2] ++ List.replicate 14 0

end VG.Test.Xts
