module

import Lean.Elab.Command
meta import Lean.Elab.Command
import VerifiedGarbageTest.Ec.OpensslEvp
meta import VerifiedGarbageTest.Ec.OpensslEvp
import VerifiedGarbage.Spec.Ecdh.BrainpoolP320r1
meta import VerifiedGarbage.Spec.Ecdh.BrainpoolP320r1

/-!
# brainpoolP320r1 public key and ECDH specification tests

RFC 7027 (and RFCs 6932, 6954 and 8734) give no vectors for 320-bit curves,
so these are OpenSSL's: the two sets of brainpoolP320r1 key pairs and shared
secrets of `evppkey_brainpool.txt` (`vectors/openssl-brainpool/`, vendored
byte for byte), `ALICE_cf_`/`BOB_cf_brainpoolP320r1` and
`ALICE_`/`BOB_brainpoolP320r1`. Their keys are PKCS #8 and SPKI PEM, decoded
here, of the curve 1.3.36.3.3.2.8.1.1.9 (RFC 5639 §4.1) with uncompressed
points; each set is checked with `Ec/OpensslEvp.lean`'s checks: each
private key's public key, both exchanges and the CAVP CDH checks of
`Ec/Cdh.lean` (invalid public and private keys), then the curve's.
-/

open Lean Elab Command in
run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "openssl-brainpool" / "evppkey_brainpool.txt")
  let C := VG.Spec.BrainpoolP320r1.curve
  -- brainpoolP320r1's object identifier (RFC 5639 §4.1).
  let oidBrainpoolP320r1 := [1, 3, 36, 3, 3, 2, 8, 1, 1, 9]
  let check : Except String Unit := do
    VG.Test.Ec.OpensslEvp.checkEcdh C oidBrainpoolP320r1
      "ALICE_cf_brainpoolP320r1" "BOB_cf_brainpoolP320r1" text
    VG.Test.Ec.OpensslEvp.checkEcdh C oidBrainpoolP320r1
      "ALICE_brainpoolP320r1" "BOB_brainpoolP320r1" text
    VG.Test.Ec.Cdh.checkCurve C
  match check with
  | .ok () => pure ()
  | .error e => throwError "evppkey_brainpool.txt: {e}"
