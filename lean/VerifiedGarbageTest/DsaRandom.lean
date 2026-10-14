import VerifiedGarbage.Spec.Dsa.RandomSign
import VerifiedGarbageTest.Dsa

/-! Regression checks for the randomized-signing contract. Small scalars are
sampler boundary cases, not cryptographic known-answer vectors. Signing's
known answer is read from the vendored NIST CAVP file. -/
namespace VG.Test.DsaRandom
open Lean Elab Command Spec.Dsa

-- Reject zero and q, then accept q-1; do not consume the suffix.
#guard Random.sample 13 128 [0, 13, 12, 9] == ⟨some 12, 3, [0, 0, 1]⟩
-- Mask excess high bits, rather than reducing modulo q.
#guard Random.sample 13 128 [255, 254, 253, 252] == ⟨some 12, 4, [0, 0, 0, 1]⟩
#guard Random.sample 13 2 [0, 13, 12] == ⟨none, 2, [0, 0, 3]⟩
#guard Random.sample 13 128 [] == ⟨none, 0, [2]⟩
#guard Random.sample 257 128 [1] == ⟨none, 0, [2]⟩
#guard Random.sample 257 128 [0, 0, 1] == ⟨none, 2, [0, 2]⟩
#guard Random.sample 0 128 [1] == ⟨none, 0, [4]⟩
#guard Random.sample 1 128 [1] == ⟨none, 0, [4]⟩
#guard Random.sample 13 0 [1] == ⟨none, 0, [3]⟩
#guard Random.drawBytes 256 == 2
#guard Random.drawBytes 255 == 1
#guard (randomSignBytes 0 0 [] [] []).status == 0

-- Exhaustive small-domain check: every accepted scalar has the same number
-- of one-byte preimages. This is a regression, not a general uniformity proof.
#guard (List.range 254).all fun i =>
  let q := i + 2
  let counts := (List.range (q - 1)).map fun j =>
    ((List.range 256).filter fun b =>
      (Random.sample q 1 [BitVec.ofNat 8 b]).scalar == some (j + 1)).length
  counts.all (· == 256 / 2 ^ bitLength q)

#assert_standard_axioms Spec.Dsa.randomSignContract
#assert_no_compiler_overrides Spec.Dsa.randomSignApi
#assert_spec_origin

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent) | throwError "no repository root"
  let text ← IO.FS.readFile (root / "vectors" / "nist-cavp-dsa" / "SigGen.txt")
  let result : Except String Unit := do
    let vs ← Dsa.parse text true
    let some v := vs.head? | throw "no signing vector"
    let pLen := (bitLength v.params.p + 7) / 8
    let qLen := (bitLength v.params.q + 7) / 8
    let key := encodeBE pLen v.params.p ++ encodeBE qLen v.params.q ++
      encodeBE pLen v.params.g ++ encodeBE pLen v.y ++ encodeBE qLen v.x
    let digest ← Dsa.digest v
    let nonce := encodeBE qLen v.k
    let expected := encodeBE qLen v.sig.r ++ encodeBE qLen v.sig.s
    let success := randomSignBytes pLen qLen key digest (nonce ++ [255])
    unless success == ⟨some expected, 1, qLen, [1, 5]⟩ do
      throw "randomized signing did not match NIST supplied nonce"
    let rejected := randomSignBytes pLen qLen key digest
      (List.replicate qLen 0 ++ encodeBE qLen v.params.q ++ nonce)
    unless rejected == ⟨some expected, 1, 3 * qLen, [0, 0, 1, 5]⟩ do
      throw "rejection sampling did not consume zero/q before NIST nonce"
    let exhausted := randomSignBytes pLen qLen key digest (nonce.take (qLen - 1))
    unless exhausted == ⟨none, 2, 0, [2]⟩ do throw "partial draw consumed"
    let limit := randomSignBytes pLen qLen key digest (List.replicate (128 * qLen) 0 ++ nonce)
    unless limit.status == 0 && limit.used == 128 * qLen do throw "draw limit ignored"
    -- Unsupported domain values fail signBytes quickly, exercising all eight
    -- attempts without embedding a fabricated signature vector.
    let badKey := List.replicate pLen 0 ++ encodeBE qLen v.params.q ++
      List.replicate (2 * pLen + qLen) 0
    let retries := randomSignBytes pLen qLen badKey digest
      ((List.replicate 9 nonce).flatten)
    unless retries.status == 0 && retries.used == 8 * qLen &&
        retries.trace == (List.replicate 8 [1, 6]).flatten ++ [3] do
      throw "signing retry limit or consumption mismatch"
  match result with
  | .ok () => pure ()
  | .error e => throwError "DSA randomized signing: {e}"

end VG.Test.DsaRandom
