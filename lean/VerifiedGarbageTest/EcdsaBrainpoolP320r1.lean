module

import Lean.Elab.Command
meta import Lean.Elab.Command
import VerifiedGarbageTest.Ec.SelfCheck
meta import VerifiedGarbageTest.Ec.SelfCheck
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Spec.Hmac
meta import VerifiedGarbage.Spec.Hmac

/-!
# ECDSA brainpoolP320r1 specification tests

No standard publishes brainpoolP320r1 ECDSA vectors: RFC 7027 (and RFCs
6932, 6954 and 8734) have none for 320-bit curves, and RFC 6979's are for
other curves. So the checks of `Ec/SelfCheck.lean`: the group law
(`[n]G = O`, `[n + 1]G = G`, `[n - 1]G = -G`, small multiples), keys and
nonces outside `[1, n - 1]`, and the signatures of `Curves.brainpoolp320r1`
with HMAC-SHA-384, which verify, and no longer once the hash, the signature
or the key changes. The curve's keys and ECDH are checked against OpenSSL's
vectors (`EcdhBrainpoolP320r1.lean`).
-/

open Lean Elab Command in
run_cmd do
  let C := VG.Spec.BrainpoolP320r1.curve
  match VG.Test.Ec.SelfCheck.checkSign C VG.Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1
      VG.Spec.Hmac.sha384 48
      (VG.Test.Ec.SelfCheck.key C "brainpoolP320r1 ECDSA")
      (VG.Test.Ec.SelfCheck.key C "brainpoolP320r1 ECDSA other") with
  | .ok () => pure ()
  | .error e => throwError "brainpoolP320r1 ECDSA: {e}"
