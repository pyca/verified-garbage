import Lean.Elab.Command
import VerifiedGarbageTest.Ec.SelfCheck
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Secp256k1Sha256

/-!
# ECDSA secp256k1 specification tests

No standard publishes secp256k1 ECDSA vectors, so the checks of
`Ec/SelfCheck.lean`: the group law (`[n]G = O`, `[n + 1]G = G`,
`[n - 1]G = -G`, small multiples), keys and nonces outside `[1, n - 1]`,
and the signatures of `Secp256k1Sha256.inst`, which verify, and no longer
once the hash, the signature or the key changes.
-/

open Lean Elab Command in
run_cmd do
  let C := VG.Spec.Secp256k1.curve
  match VG.Test.Ec.SelfCheck.checkSign C VG.Spec.Ecdsa.Rfc6979.Secp256k1Sha256.inst
      (VG.Test.Ec.SelfCheck.key C "secp256k1 ECDSA") (VG.Test.Ec.SelfCheck.key C "secp256k1 ECDSA other") with
  | .ok () => pure ()
  | .error e => throwError "secp256k1 ECDSA: {e}"
