import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
import VerifiedGarbage.Spec.Ecdsa.P192

/-!
# Deterministic ECDSA over P-192 with HMAC-SHA-256: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of P-192
(`Spec/Ecdsa/P192.lean`) with SHA-256: `vg_ecdsa_p192_sha256_sign`, in the
module `ecdsa_p192_sha256`. At most 8 candidates: each is unsuitable with
probability under `2^-96` (`n > 2^192 - 2^95`), so all 8 with
probability under `2^-768`.
-/

namespace VG.Spec.Ecdsa.Rfc6979.P192Sha256

/-- P-192 with HMAC-SHA-256. -/
def inst : Instance where
  ecdsa := Ecdsa.P192.inst
  hash := Hmac.sha256
  hashLen := 32
  hashName := "sha256"
  hashTitle := "SHA-256"
  tries := 8

/-- `vg_ecdsa_p192_sha256_sign` on every target. -/
def signApi : Api := inst.signApi

end VG.Spec.Ecdsa.Rfc6979.P192Sha256
