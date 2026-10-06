import Lean.Elab.Command
import VerifiedGarbageTest.Ec.Wycheproof
import VerifiedGarbage.Spec.Ecdsa.Verify.Secp256k1
import VerifiedGarbage.Spec.Sha256

/-!
# ECDSA secp256k1 signature verification specification tests

Wycheproof's secp256k1 ECDSA vectors with SHA-256 and IEEE P1363 signatures
(`ecdsa_secp256k1_sha256_p1363_test.json`, vendored byte for byte) whose
signature has 64 octets: 167 valid and 67 invalid, with the checks of
`Ec/Wycheproof.lean`.
-/

open Lean Elab Command in
run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "wycheproof-ecdsa-secp256k1" /
    "ecdsa_secp256k1_sha256_p1363_test.json")
  match VG.Test.Ec.Wycheproof.checkVerify VG.Spec.Secp256k1.curve VG.Spec.Sha256.hash 167 67
      text with
  | .ok () => pure ()
  | .error e => throwError "ecdsa_secp256k1_sha256_p1363_test.json: {e}"
