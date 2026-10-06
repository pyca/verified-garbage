import Lean.Elab.Command
import VerifiedGarbageTest.Ec.Rfc7027
import VerifiedGarbage.Spec.Ecdh.BrainpoolP384r1

/-!
# brainpoolP384r1 public key and ECDH specification tests

The two key pairs and the shared point of RFC 7027 §A.2 (brainpoolP384r1), parsed
from the byte-for-byte vendored RFC, with the checks of `Ec/Rfc7027.lean`.
-/

open Lean Elab Command in
run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "rfc7027" / "rfc7027.txt")
  match (VG.Test.Ec.Rfc7027.checkEcdh VG.Spec.BrainpoolP384r1.curve "A.2.  384-Bit Curve" "A.3.") text with
  | .ok () => pure ()
  | .error e => throwError "rfc7027.txt: {e}"
