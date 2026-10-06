import Lean.Elab.Command
import VerifiedGarbageTest.Ec.Wycheproof
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Secp256k1Sha256

/-!
# ECDSA secp256k1 specification tests

With the private key of the first vector (`tcId` 1, valid) of Wycheproof's
secp256k1 ECDH vectors (`ecdh_secp256k1_test.json`, vendored byte for byte),
the checks of `Ec/Wycheproof.lean`: the group law and keys, and the
signatures of `Secp256k1Sha256.inst`, which verify.
-/

open Lean Elab Command in
run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile
    (root / "vectors" / "wycheproof-ecdh-secp256k1" / "ecdh_secp256k1_test.json")
  let r := do
    let j ← Json.parse text
    let t ← ((← (← j.getObjVal? "testGroups").getArrVal? 0).getObjVal? "tests") >>= (·.getArrVal? 0)
    let d ← VG.Test.Ec.hexNat (← t.getObjValAs? String "private")
    VG.Test.Ec.Wycheproof.checkSign VG.Spec.Secp256k1.curve
      VG.Spec.Ecdsa.Rfc6979.Secp256k1Sha256.inst d
  match r with
  | .ok () => pure ()
  | .error e => throwError "ecdh_secp256k1_test.json: {e}"
