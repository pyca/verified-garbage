import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
import VerifiedGarbage.Spec.Ecdsa.P384

/-!
# Deterministic ECDSA over P-384 with HMAC-SHA-384: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of P-384
(`Spec/Ecdsa/P384.lean`) with SHA-384: `vg_ecdsa_p384_sha384_sign`, in the
module `ecdsa_p384_sha384`. At most 8 candidates: each is unsuitable with
probability under `2^-193` (`n > 2^384 - 2^190`), so all 8 with
probability under `2^-1544`.
-/

namespace VG.Spec.Ecdsa.Rfc6979.P384Sha384

/-- P-384 with HMAC-SHA-384. -/
def inst : Instance where
  ecdsa := Ecdsa.P384.inst
  hash := Hmac.sha384
  hashLen := 48
  hashName := "sha384"
  hashTitle := "SHA-384"
  tries := 8

/-- `vg_ecdsa_p384_sha384_sign` on every target. -/
def signApi : Api := inst.signApi

end VG.Spec.Ecdsa.Rfc6979.P384Sha384
