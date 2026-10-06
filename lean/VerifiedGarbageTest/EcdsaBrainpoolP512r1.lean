import Lean.Elab.Command
import VerifiedGarbageTest.Ec.Rfc7027
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512

/-!
# ECDSA brainpoolP512r1 specification tests

The first key pair of RFC 7027 §A.3 (brainpoolP512r1), parsed from the
byte-for-byte vendored RFC, with the checks of `Ec/Rfc7027.lean`: the group
law, and the signatures of `BrainpoolP512r1Sha512.inst`, which verify.
-/

open Lean Elab Command in
run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "rfc7027" / "rfc7027.txt")
  match (VG.Test.Ec.Rfc7027.checkEcdsa VG.Spec.BrainpoolP512r1.curve
      VG.Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst
      "A.3.  512-Bit Curve" "Authors") text with
  | .ok () => pure ()
  | .error e => throwError "rfc7027.txt: {e}"
