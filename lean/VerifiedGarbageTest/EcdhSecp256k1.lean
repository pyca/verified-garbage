import Lean.Elab.Command
import VerifiedGarbageTest.Ec.Wycheproof
import VerifiedGarbage.Spec.Ecdh.Secp256k1

/-!
# secp256k1 public key and ECDH specification tests

Wycheproof's secp256k1 ECDH vectors (`ecdh_secp256k1_test.json`, vendored
byte for byte) whose public key is an uncompressed point under the
algorithm identifier `id-ecPublicKey` with the named curve `secp256k1`: 473
valid and 18 invalid (points off the curve), with the checks of
`Ec/Wycheproof.lean`.
-/

open Lean Elab Command in
run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile
    (root / "vectors" / "wycheproof-ecdh-secp256k1" / "ecdh_secp256k1_test.json")
  -- `SubjectPublicKeyInfo` up to the point: `id-ecPublicKey` (1.2.840.10045.2.1),
  -- `secp256k1` (1.3.132.0.10), and the bit string's header.
  let spki ← match VG.Test.Ec.hexBytes "3056301006072a8648ce3d020106052b8104000a034200" with
    | .ok b => pure b
    | .error e => throwError e
  match VG.Test.Ec.Wycheproof.checkEcdh VG.Spec.Secp256k1.curve spki 473 18 text with
  | .ok _ => pure ()
  | .error e => throwError "ecdh_secp256k1_test.json: {e}"
