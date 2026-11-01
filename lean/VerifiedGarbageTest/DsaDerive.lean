module

import VerifiedGarbage.Spec.Dsa.Derive
meta import VerifiedGarbage.Spec.Dsa.Derive
import VerifiedGarbageTest.Dsa
meta import VerifiedGarbageTest.Dsa

/-! Tests for the domain check and key derivation that key generation calls.
Known answers come from the NIST signing vectors' published x and y; each
is checked against `generateKeyBytes` with the same x as its first draw. -/
namespace VG.Test.DsaDerive
open Lean Elab Command Spec.Dsa

#guard checkParametersBytes 0 0 [] == false
#guard checkParametersBytes 128 20 [] == false
#guard checkParametersBytes 128 20 (List.replicate 276 0) == false
#guard deriveKeyBytes 128 20 [] [] == none
#guard deriveKeyBytes 128 20 (List.replicate 276 0) (List.replicate 20 1) == none

#assert_standard_axioms Spec.Dsa.checkParametersContract
#assert_standard_axioms Spec.Dsa.deriveKeyContract
#assert_no_compiler_overrides Spec.Dsa.checkParametersApi Spec.Dsa.deriveKeyApi
#assert_spec_origin

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent) | throwError "no repository root"
  let text ← IO.FS.readFile (root / "vectors" / "nist-cavp-dsa" / "SigGen.txt")
  let result : Except String Unit := do
    let vs ← Dsa.parse text true
    for (pLen, qLen) in [(128, 20), (256, 28), (256, 32), (384, 32)] do
      let some v := vs.find? (fun v => bitLength v.params.p == 8 * pLen &&
          bitLength v.params.q == 8 * qLen) | throw "missing NIST key size"
      let params := encodeBE pLen v.params.p ++ encodeBE qLen v.params.q ++ encodeBE pLen v.params.g
      let expected := params ++ encodeBE pLen v.y ++ encodeBE qLen v.x
      unless checkParametersBytes pLen qLen params do throw "NIST domain rejected"
      unless (generateKeyBytes pLen qLen params []).trace == [2] do
        throw "key generation rejected a domain the check accepts"
      -- A generator of order other than q: g = p - 1 has order 2.
      let badG := encodeBE pLen v.params.p ++ encodeBE qLen v.params.q ++ encodeBE pLen (v.params.p - 1)
      if checkParametersBytes pLen qLen badG then throw "accepted g of order 2"
      unless generateKeyBytes pLen qLen badG (encodeBE qLen v.x) == ⟨none, 0, 0, [4]⟩ do
        throw "key generation accepted a domain the check rejects"
      if checkParametersBytes pLen qLen (params.take (params.length - 1)) then
        throw "accepted a short domain"
      let x := encodeBE qLen v.x
      unless deriveKeyBytes pLen qLen params x == some expected do throw "NIST key derivation mismatch"
      unless (generateKeyBytes pLen qLen params x).key == deriveKeyBytes pLen qLen params x do
        throw "derivation differs from key generation's first accepted draw"
      unless deriveKeyBytes pLen qLen params (encodeBE qLen 0) == none do throw "accepted x = 0"
      unless deriveKeyBytes pLen qLen params (encodeBE qLen v.params.q) == none do throw "accepted x = q"
      unless deriveKeyBytes pLen qLen params (x.take (qLen - 1)) == none do throw "accepted a short x"
      unless deriveKeyBytes pLen qLen badG x == none do throw "derived a key in a rejected domain"
  match result with
  | .ok () => pure ()
  | .error e => throwError "DSA derivation: {e}"

end VG.Test.DsaDerive
