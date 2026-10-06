import Lean.Elab.Command
import VerifiedGarbageTest.Ec.Rfc7027
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256

/-!
# ECDSA brainpoolP256r1 specification tests

The first key pair of RFC 7027 §A.1 (brainpoolP256r1), parsed from the
byte-for-byte vendored RFC, with the checks of `Ec/Rfc7027.lean`: the group
law, and the signatures of `BrainpoolP256r1Sha256.inst`, which verify.
-/

open Lean Elab Command in
run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "rfc7027" / "rfc7027.txt")
  match (VG.Test.Ec.Rfc7027.checkEcdsa VG.Spec.BrainpoolP256r1.curve
      VG.Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst
      "A.1.  256-Bit Curve" "A.2.") text with
  | .ok () => pure ()
  | .error e => throwError "rfc7027.txt: {e}"
