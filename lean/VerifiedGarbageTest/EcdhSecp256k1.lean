import Lean.Elab.Command
import VerifiedGarbageTest.Ec.SelfCheck
import VerifiedGarbage.Spec.Ecdh.Secp256k1

/-!
# secp256k1 public key and ECDH specification tests

No standard publishes secp256k1 ECDH vectors, so the checks of
`Ec/SelfCheck.lean`: the exchange of two key pairs, both ways and by
`[a b mod n]G`, invalid public and private keys, and the curve's
parameters (`G` on the curve, `[n - 1]G = -G`).
-/

open Lean Elab Command in
run_cmd do
  let C := VG.Spec.Secp256k1.curve
  match VG.Test.Ec.SelfCheck.checkEcdh C (VG.Test.Ec.SelfCheck.key C "secp256k1 ECDH A")
      (VG.Test.Ec.SelfCheck.key C "secp256k1 ECDH B") with
  | .ok () => pure ()
  | .error e => throwError "secp256k1 ECDH: {e}"
