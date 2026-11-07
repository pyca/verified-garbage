module

import VerifiedGarbage.Spec.Dsa.Generate
meta import VerifiedGarbage.Spec.Dsa.Generate
import VerifiedGarbageTest.Dsa
meta import VerifiedGarbageTest.Dsa

/-! Tests for the byte-level key-generation contract and the generation
helpers. Key-generation known answers come from the NIST signing vectors'
published x and y components. -/
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
#guard ¬generationLengthsValid 256 20
#guard ¬generationLengthsValid 256 28
#guard lengthsValid 256 28
#guard generateKeyBytes 0 0 [] [] == ⟨none, 0, 0, [4]⟩
#guard generateKeyBytes 128 20 [] [] == ⟨none, 0, 0, [4]⟩
#guard generateKeyBytes 128 20 (List.replicate 276 0) [] == ⟨none, 0, 0, [4]⟩

#assert_standard_axioms Spec.Dsa.generateKeyContract
#assert_no_compiler_overrides Spec.Dsa.generateKeyApi
#assert_spec_origin

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent) | throwError "no repository root"
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
