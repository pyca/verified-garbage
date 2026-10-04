import Lean.Elab.Command
import VerifiedGarbageTest.Ec.RfcSign
import VerifiedGarbage.Spec.Ecdsa.P256

/-!
# ECDSA P-256 specification tests

The key pair and the ten signatures of RFC 6979 §A.2.5 (NIST P-256, the
messages "sample" and "test" with SHA-1, SHA-224, SHA-256, SHA-384 and
SHA-512), parsed from the byte-for-byte vendored RFC, with the checks of
`Ec/RfcSign.lean`.
-/

open Lean Elab Command in
run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "rfc6979" / "rfc6979.txt")
  match (VG.Test.Ec.RfcSign.check VG.Spec.P256.curve "A.2.5.  ECDSA, 256 Bits" "A.2.6.") text with
  | .ok () => pure ()
  | .error e => throwError "rfc6979.txt: {e}"
