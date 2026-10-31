module

import VerifiedGarbage.Spec.Dsa.Generate
meta import VerifiedGarbage.Spec.Dsa.Generate
import VerifiedGarbageTest.Dsa
meta import VerifiedGarbageTest.Dsa

/-! Tests for the byte-level generation contracts. Key-generation known
answers come from the NIST signing vectors' published x and y components.
Parameter candidate known answers and primality tests are inherited from
Dsa. This adapter does not introduce another parameter-generation algorithm. -/
namespace VG.Test.DsaGenerate
open Lean Elab Command Spec.Dsa

#guard generationChunks 2 [1, 2, 3, 4, 5] == [[1, 2], [3, 4]]
#guard generationChunks 0 [1, 2] == []
#guard generationChunks 2 [] == []
#guard generationLengthsValid 128 20
#guard generationLengthsValid 256 32
#guard generationLengthsValid 384 32
-- The legacy import extension must not change parameter-generation policy.
#guard supportedSizes 2048 160
#guard lengthsValid 256 20
#guard ¬supportedSizes 1024 224
#guard ¬supportedSizes 3072 160
#guard ¬lengthsValid 128 28
#guard ¬lengthsValid 384 20
#guard subgroupBits 2048 == some 256
#guard ¬generationLengthsValid 256 20
#guard generateParametersBytes 256 20 [] [] [] == none
#guard ¬generationLengthsValid 256 28
#guard lengthsValid 256 28
#guard generateParametersBytes 256 28 [] [] [] == none
#guard generateParametersBytes 128 20 [1] [] [] == none
#guard generateParametersBytes 128 20 [] [1] [] == none
#guard generateParametersBytes 128 20 [] [] [] == none
#guard generateParametersBytes 256 32 [] [] [] == none
#guard generateParametersBytes 384 32 [] [] [] == none
#guard generateKeyBytes 0 0 [] [] == ⟨none, 0, 0, [4]⟩
#guard generateKeyBytes 128 20 [] [] == ⟨none, 0, 0, [4]⟩
#guard generateKeyBytes 128 20 (List.replicate 276 0) [] == ⟨none, 0, 0, [4]⟩

/-- A full parameter-generation run from a published seed. Fixed witness
bytes make this a reproducible algorithm regression, not a probabilistic
primality argument. Only the first short-search SHA-1 vector is used. -/
def checkParameters (text : String) : Except String Unit := do
  let mut selected := false
  let mut p := 0
  let mut q := 0
  let mut seed := []
  for raw in (text.splitOn "\n").takeWhile (!·.startsWith "[A.1.2") do
    if raw.startsWith "\t" then continue
    let line := raw.trimAscii.toString
    if line.startsWith "[mod = " then
      selected := line == "[mod = L=1024, N=160, SHA-1]"
    else if selected then
      match line.splitOn " = " with
      | ["P", value] => p := decodeBE (← Dsa.hex value)
      | ["Q", value] => q := decodeBE (← Dsa.hex value)
      | ["domain_parameter_seed", value] => seed := ← Dsa.hex value
      | ["counter", value] =>
        let some counter := value.toNat? | throw "invalid counter"
        if counter ≤ 50 then
          let tape := List.replicate 65536 (2 : Byte)
          let some out := generateParametersBytes 128 20 seed (encodeBE 128 2) tape
            | throw "published seed failed parameter generation"
          unless out.length == 276 do throw "wrong parameter output width"
          let a := paramsBytes 128 20 out
          unless a.p == p && a.q == q && decide (parametersValid a) do
            throw "generated parameters disagree with NIST p/q or fail domain checks"
          unless generateParametersBytes 128 20 seed (encodeBE 128 2) [] == none do
            throw "parameter generation ignored exhausted witnesses"
          return ()
      | _ => pure ()
  throw "missing short-search NIST parameter vector"

#assert_standard_axioms Spec.Dsa.generateKeyContract
#assert_standard_axioms Spec.Dsa.generateParametersContract
#assert_no_compiler_overrides Spec.Dsa.generateKeyApi Spec.Dsa.generateParametersApi
#assert_spec_origin

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent) | throwError "no repository root"
  let parameters ← IO.FS.readFile (root / "vectors" / "nist-cavp-dsa" / "PQGGen.txt")
  match checkParameters parameters with
  | .ok () => pure ()
  | .error e => throwError "DSA parameter generation: {e}"
  let text ← IO.FS.readFile (root / "vectors" / "nist-cavp-dsa" / "SigGen.txt")
  let result : Except String Unit := do
    let vs ← Dsa.parse text true
    -- Exercise each supported (L,N), including import-only (2048,224).
    for (pLen, qLen) in [(128, 20), (256, 28), (256, 32), (384, 32)] do
      let some v := vs.find? (fun v => bitLength v.params.p == 8 * pLen &&
          bitLength v.params.q == 8 * qLen) | throw "missing NIST key size"
      let params := encodeBE pLen v.params.p ++ encodeBE qLen v.params.q ++ encodeBE pLen v.params.g
      unless paramsBytes pLen qLen params == v.params do throw "parameter decoding mismatch"
      let expected := params ++ encodeBE pLen v.y ++ encodeBE qLen v.x
      let rand := encodeBE qLen v.x
      let key := generateKeyBytes pLen qLen params (rand ++ [255])
      unless key == ⟨some expected, 1, qLen, [1, 5]⟩ do throw "NIST key generation mismatch"
      unless privateKeyBytes pLen qLen expected == ⟨v.params, v.y, some v.x⟩ do
        throw "generated key incompatible with signer encoding"
      -- A 224-bit q may be imported in a padded 32-byte field. Sampling
      -- still consumes 28 bytes, while output preserves the padded width.
      if qLen == 28 then
        let padded := encodeBE pLen v.params.p ++ encodeBE 32 v.params.q ++ encodeBE pLen v.params.g
        let paddedKey := padded ++ encodeBE pLen v.y ++ encodeBE 32 v.x
        unless generateKeyBytes pLen 32 padded rand == ⟨some paddedKey, 1, 28, [1, 5]⟩ do
          throw "padded subgroup changed random draw width"
      let rejected := generateKeyBytes pLen qLen params
        (List.replicate qLen 0 ++ encodeBE qLen v.params.q ++ rand)
      unless rejected == ⟨some expected, 1, 3 * qLen, [0, 0, 1, 5]⟩ do
        throw "key sampler accepted zero/q or consumed suffix"
      unless generateKeyBytes pLen qLen params (rand.take (qLen - 1)) == ⟨none, 2, 0, [2]⟩ do
        throw "key sampler consumed partial draw"
      let limit := generateKeyBytes pLen qLen params (List.replicate (128 * qLen) 0 ++ rand)
      unless limit.status == 0 && limit.used == 128 * qLen do throw "key draw bound ignored"
  match result with
  | .ok () => pure ()
  | .error e => throwError "DSA generation: {e}"

end VG.Test.DsaGenerate
