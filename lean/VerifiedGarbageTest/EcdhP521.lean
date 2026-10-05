import Lean.Elab.Command
import VerifiedGarbageTest.Ec.Cdh
import VerifiedGarbage.Spec.Ecdh.P521

/-!
# P-521 public key and ECDH specification tests

The 25 P-521 vectors of NIST CAVP's SP 800-56A ECC CDH primitive test
(`KAS_ECC_CDH_PrimitiveTest.txt`, vendored byte for byte), with the checks
of `Ec/Cdh.lean`.
-/

open Lean Elab Command in
run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "nist-cavp" / "ecc-cdh" / "KAS_ECC_CDH_PrimitiveTest.txt")
  match (VG.Test.Ec.Cdh.check VG.Spec.P521.curve "P-521" 25) text with
  | .ok () => pure ()
  | .error e => throwError "KAS_ECC_CDH_PrimitiveTest.txt: {e}"
