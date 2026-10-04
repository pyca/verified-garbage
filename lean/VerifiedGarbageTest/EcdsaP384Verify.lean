import Lean.Elab.Command
import VerifiedGarbageTest.Ec.SigVer
import VerifiedGarbage.Spec.Ecdsa.Verify.P384

/-!
# ECDSA P-384 signature verification specification tests

The 75 P-384 vectors of NIST CAVP's ECDSA signature verification test
(`SigVer.rsp`, vendored byte for byte), 15 with each of SHA-1, SHA-224,
SHA-256, SHA-384 and SHA-512, with the checks of `Ec/SigVer.lean`.
-/

open Lean Elab Command in
run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "nist-cavp-ecdsa" / "SigVer.rsp")
  match (VG.Test.Ec.SigVer.check VG.Spec.P384.curve "P-384" 75) text with
  | .ok () => pure ()
  | .error e => throwError "SigVer.rsp: {e}"
