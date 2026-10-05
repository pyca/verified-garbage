import Lean.Elab.Command
import VerifiedGarbageTest.Ec.Rfc6979
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P224Sha224

/-!
# Deterministic ECDSA (RFC 6979) over P-224: specification tests

The ten signatures of RFC 6979 §A.2.4 (NIST P-224; "sample" and "test"
with SHA-1, SHA-224, SHA-256, SHA-384 and SHA-512), parsed from the
byte-for-byte vendored RFC, with the checks of `Ec/Rfc6979.lean`: the
contract's instance is `P224Sha224.inst`.
-/

open Lean Elab Command in
run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "rfc6979" / "rfc6979.txt")
  match (VG.Test.Ec.Rfc6979.check VG.Spec.P224.curve
      [("SHA-224", VG.Spec.Ecdsa.Rfc6979.P224Sha224.inst)] "A.2.4.  ECDSA, 224 Bits" "A.2.5.") text with
  | .ok () => pure ()
  | .error e => throwError "rfc6979.txt: {e}"
